import os
import re
import sys
import time
import html
import asyncio
import threading
import urllib.request
from collections import defaultdict
from datetime import datetime, timedelta, timezone

from flask import Flask
from telethon import TelegramClient, events, utils
from telethon.errors import FloodWaitError, UserAlreadyParticipantError
from telethon.sessions import StringSession
from telethon.tl.functions.account import UpdateStatusRequest
from telethon.tl.functions.channels import JoinChannelRequest
from telethon.tl.functions.messages import ImportChatInviteRequest
from telethon.tl.types import MessageEntityTextUrl


def env_flag(name, default):
    return os.environ.get(name, str(default)).strip().lower() in ("1", "true", "yes", "on")


def parse_channel(value):
    value = re.sub(r"^(?:https?://)?(?:t\.me|telegram\.me)/", "", value.strip())
    value = value.lstrip("@").split("/")[0]
    return int(value) if value.lstrip("-").isdigit() else value


API_ID = int(os.environ.get("API_ID") or 0)
API_HASH = os.environ.get("API_HASH", "")
SESSION_STRING = os.environ.get("SESSION_STRING", "")
PORT = int(os.environ.get("PORT", 8080))

TARGET_CHANNELS = [
    parse_channel(c)
    for c in os.environ.get("TARGET_CHANNELS", "").split(",")
    if c.strip()
]

DEFAULT_BOT = os.environ.get("TARGET_BOT", "xrocket")
BOT_ALIASES = {"xrocket", "tonrocketbot"}
POLL_INTERVAL = float(os.environ.get("POLL_INTERVAL", 1.5))
ONLINE_INTERVAL = float(os.environ.get("ONLINE_INTERVAL", 25))
PING_INTERVAL = float(os.environ.get("PING_INTERVAL", 300))
REPLY_TIMEOUT = float(os.environ.get("REPLY_TIMEOUT", 6))
MAX_ROUNDS = int(os.environ.get("MAX_ROUNDS", 4))
AUTO_JOIN = env_flag("AUTO_JOIN", True)
JOIN_TARGETS = env_flag("JOIN_TARGETS", True)
SELF_PING = env_flag("SELF_PING", True)
LOCAL_TZ = timezone(timedelta(hours=float(os.environ.get("TZ_OFFSET_HOURS", 6))))

LINK_PATTERNS = [
    re.compile(
        r"(?:https?://)?(?:t\.me|telegram\.me)/([A-Za-z0-9_]+)\?(?:[^#\s'\"]*&)?(?:start|startapp)=([A-Za-z0-9_-]+)",
        re.I,
    ),
    re.compile(
        r"tg://resolve\?domain=([A-Za-z0-9_]+)&(?:[^#\s'\"]*&)?(?:start|startapp)=([A-Za-z0-9_-]+)",
        re.I,
    ),
]

CHEQUE_TEXT_RE = re.compile(r"Cheque for\s+([\d.,]+)\s+(\S+)(?:\s*\(([\d.,]+)\s*\$\))?", re.I)
RECEIVE_RE = re.compile(r"Receive\s+([\d.,]+)\s+(\S+)", re.I)

SUCCESS_WORDS = ["you received", "you got", "received", "claimed", "activated", "получили", "получено", "вы получили", "успешно", "активирован"]
EXPIRED_WORDS = ["already", "expired", "not found", "empty", "no longer", "уже", "истек", "не найден", "закончил", "закончились"]
PREMIUM_WORDS = ["premium", "премиум"]
CAPTCHA_WORDS = ["captcha", "капча"]
CHECK_WORDS = ["check", "claim", "done", "subscribed", "activate", "receive", "проверить", "получить", "готово", "подписал", "активировать", "✅"]

STATUS_LABEL = {
    "claimed": ("✅", "Cheque Claimed"),
    "expired": ("⏳", "Expired / Already Claimed"),
    "premium": ("💎", "Premium Required"),
    "captcha": ("🧩", "Captcha Required"),
    "unknown": ("❔", "Unknown Bot Reply"),
    "no_reply": ("📭", "Bot Did Not Reply"),
    "error": ("⚠️", "Send Error"),
}

app = Flask(__name__)


@app.route("/")
def home():
    return "⚡ xRocket Sniper is Running 24/7!"


def run_flask():
    app.run(host="0.0.0.0", port=PORT)


def fmt_time(ts):
    return datetime.fromtimestamp(ts, LOCAL_TZ).strftime("%H:%M:%S.%f")[:-3]


def fmt_ms(seconds):
    ms = seconds * 1000
    return f"{ms / 1000:.2f} s" if ms >= 1000 else f"{ms:.0f} ms"


def classify(text):
    low = text.lower()
    expired = any(w in low for w in EXPIRED_WORDS)
    if any(w in low for w in SUCCESS_WORDS) and not expired:
        return "claimed"
    if any(w in low for w in PREMIUM_WORDS):
        return "premium"
    if any(w in low for w in CAPTCHA_WORDS):
        return "captcha"
    if expired:
        return "expired"
    return None


def parse_reward(msg):
    m = CHEQUE_TEXT_RE.search(msg.raw_text or "")
    if m:
        return m.group(1), m.group(2), m.group(3) or ""
    for row in msg.buttons or []:
        for btn in row:
            m = RECEIVE_RE.search(btn.text or "")
            if m:
                return m.group(1), m.group(2), ""
    return "", "", ""


def fetch_url(url):
    urllib.request.urlopen(url, timeout=10).read()


class XRocketSniper:
    def __init__(self, session, api_id, api_hash):
        self.client = TelegramClient(
            StringSession(session),
            api_id,
            api_hash,
            connection_retries=None,
            retry_delay=1,
            auto_reconnect=True,
        )
        self.client.flood_sleep_threshold = 0
        self.processed_posts = set()
        self.fired = set()
        self.tasks = set()
        self.channel_entities = {}
        self.titles = {}
        self.bot_entity = None
        self.inbox = {}
        self.inbox_seq = 0
        self.result_lock = asyncio.Lock()
        self.started_at = time.time()
        self.stats = defaultdict(int)
        self.by_channel = defaultdict(lambda: defaultdict(int))
        self.by_coin = defaultdict(float)
        self.claim_times = []

    def spawn(self, coro):
        task = asyncio.create_task(coro)
        self.tasks.add(task)
        task.add_done_callback(self.tasks.discard)
        return task

    async def send_log(self, text):
        try:
            await self.client.send_message("me", text, parse_mode="html")
        except Exception as err:
            print(f"[!] Log error: {err}")

    def log(self, text):
        self.spawn(self.send_log(text))

    def extract_payload(self, msg):
        parts = [msg.raw_text or ""]
        for row in msg.buttons or []:
            for btn in row:
                parts.append(str(btn.button))
        for ent in msg.entities or []:
            if isinstance(ent, MessageEntityTextUrl) and ent.url:
                parts.append(ent.url)
        blob = "\n".join(parts)

        low = blob.lower()
        if not any(alias in low for alias in BOT_ALIASES):
            return None

        for pattern in LINK_PATTERNS:
            for m in pattern.finditer(blob):
                if m.group(1).lower() in BOT_ALIASES:
                    return m.group(2)
        return None

    async def join(self, url):
        invite = re.search(r"t\.me/(?:\+|joinchat/)([A-Za-z0-9_-]+)", url)
        try:
            if invite:
                await self.client(ImportChatInviteRequest(invite.group(1)))
            else:
                m = re.search(r"t\.me/([A-Za-z0-9_]{4,})", url)
                if not m:
                    return False
                name = m.group(1)
                if name.lower().endswith("bot") or name.lower() in BOT_ALIASES:
                    return False
                await self.client(JoinChannelRequest(name))
            self.stats["joined"] += 1
            print(f"[+] Joined: {url}")
            return True
        except UserAlreadyParticipantError:
            return True
        except FloodWaitError as err:
            await asyncio.sleep(err.seconds)
            return False
        except Exception as err:
            print(f"[-] Join failed ({url}): {err}")
            return False

    def store_inbox(self, msg):
        self.inbox_seq += 1
        self.inbox[msg.id] = (msg, time.time(), self.inbox_seq)

    async def on_bot_msg(self, event):
        self.store_inbox(event.message)

    async def wait_inbox(self, sent_id, min_seq):
        loop = asyncio.get_event_loop()
        end = loop.time() + REPLY_TIMEOUT
        while loop.time() < end:
            fresh = [e for mid, e in self.inbox.items() if mid > sent_id and e[2] > min_seq]
            if fresh:
                return max(fresh, key=lambda e: e[2])
            await asyncio.sleep(0.05)
        return None

    async def act_on_buttons(self, msg):
        acted = False
        joined = False
        click_pos = None

        for i, row in enumerate(msg.buttons or []):
            for j, btn in enumerate(row):
                url = getattr(btn.button, "url", None)
                kind = type(btn.button).__name__
                if url and "WebView" not in kind:
                    if AUTO_JOIN and "t.me/" in url and await self.join(url):
                        acted = joined = True
                        await asyncio.sleep(1)
                elif btn.data is not None and click_pos is None:
                    if any(w in (btn.text or "").lower() for w in CHECK_WORDS):
                        click_pos = (i, j)

        if joined:
            await asyncio.sleep(0.6)

        if click_pos:
            try:
                await msg.click(*click_pos)
                acted = True
            except FloodWaitError as err:
                await asyncio.sleep(err.seconds)
            except Exception as err:
                print(f"[-] Click failed: {err}")

        return acted

    async def resolve(self, sent_id, seq_at_send):
        min_seq = seq_at_send
        last_text, last_ts = "", time.time()

        for _ in range(MAX_ROUNDS):
            entry = await self.wait_inbox(sent_id, min_seq)
            if not entry:
                return ("no_reply" if not last_text else "unknown"), last_text, last_ts

            msg, recv_ts, seq = entry
            text = msg.raw_text or ""
            last_text, last_ts = text, recv_ts

            status = classify(text)
            if status:
                return status, text, recv_ts

            min_seq = self.inbox_seq
            if not await self.act_on_buttons(msg):
                return "unknown", text, recv_ts

        return "unknown", last_text, last_ts

    async def fire_claim(self, info):
        key = info["payload"]
        if key in self.fired:
            return
        self.fired.add(key)

        self.stats["detected"] += 1
        self.by_channel[info["title"]]["detected"] += 1

        dest = self.bot_entity or DEFAULT_BOT
        seq_at_send = self.inbox_seq

        try:
            sent = await self.client.send_message(dest, f"/start {info['payload']}")
            info["sent_ts"] = time.time()
            print(f"\n[⚡ SENT] /start {info['payload']} | {info['title']} | {fmt_ms(info['sent_ts'] - info['seen_ts'])}")
        except FloodWaitError as err:
            self.fired.discard(key)
            self.stats["error"] += 1
            self.report(info, "error", f"FloodWait {err.seconds}s", time.time())
            return
        except Exception as err:
            self.fired.discard(key)
            self.stats["error"] += 1
            self.report(info, "error", str(err), time.time())
            return

        async with self.result_lock:
            status, text, result_ts = await self.resolve(sent.id, seq_at_send)

        self.report(info, status, text, result_ts)

    def report(self, info, status, text, result_ts):
        self.stats[status] += 1
        title = info["title"]
        amount, coin = info["amount"], info["coin"]

        if status == "claimed":
            self.by_channel[title]["claimed"] += 1
            self.claim_times.append(result_ts - info["sent_ts"])
            if amount and coin:
                try:
                    self.by_coin[coin] += float(amount.replace(",", ""))
                except ValueError:
                    pass

        emoji, label = STATUS_LABEL.get(status, ("❔", status))
        reward = f"{amount} {coin}".strip() or "N/A"
        usd = f" (≈ ${info['usd']})" if info["usd"] else ""
        sent_ts = info.get("sent_ts")

        lines = [
            f"{emoji} <b>{label}</b>",
            "━━━━━━━━━━━━━━━━━━━",
            f"📢 Channel: <b>{html.escape(title)}</b>",
            f"💰 Reward: <b>{html.escape(reward)}</b>{usd}",
            f"🔑 Payload: <code>{html.escape(info['payload'])}</code>",
            f"📝 Post ID: <code>{info['msg_id']}</code>",
            f"📡 Source: {info['source']}",
            "",
            "🕒 <b>Timeline</b> (UTC+6)",
            f"• Posted: <code>{info['post_dt'].astimezone(LOCAL_TZ).strftime('%H:%M:%S')}</code>",
            f"• Seen: <code>{fmt_time(info['seen_ts'])}</code>",
        ]
        if sent_ts:
            lines.append(f"• Clicked/Sent: <code>{fmt_time(sent_ts)}</code>")
        lines.append(f"• Result: <code>{fmt_time(result_ts)}</code>")

        lines += ["", "⚡ <b>Latency</b>"]
        lines.append(f"• Post → Seen: ~{fmt_ms(max(0, info['seen_ts'] - info['post_dt'].timestamp()))}")
        if sent_ts:
            lines.append(f"• Seen → Sent: {fmt_ms(sent_ts - info['seen_ts'])}")
            lines.append(f"• Sent → Result: {fmt_ms(max(0, result_ts - sent_ts))}")
        lines.append(f"• Total (Post → Result): ~{fmt_ms(max(0, result_ts - info['post_dt'].timestamp()))}")

        snippet = (text or "").strip().replace("\n", " ")[:180]
        if snippet:
            lines += ["", f"🤖 Bot: {html.escape(snippet)}"]

        lines += ["", f"📊 Total claimed: <b>{self.stats['claimed']}</b> / detected {self.stats['detected']}"]

        print(f"[{label}] {reward} | {title}")
        self.log("\n".join(lines))

    def summary_text(self):
        uptime = timedelta(seconds=int(time.time() - self.started_at))
        s = self.stats
        lines = [
            "📊 <b>Sniper Stats</b>",
            "━━━━━━━━━━━━━━━━━━━",
            f"⏱ Uptime: <code>{uptime}</code>",
            f"🎯 Detected: <code>{s['detected']}</code>",
            f"✅ Claimed: <code>{s['claimed']}</code>",
            f"⏳ Expired: <code>{s['expired']}</code>",
            f"💎 Premium: <code>{s['premium']}</code>",
            f"🧩 Captcha: <code>{s['captcha']}</code>",
            f"❔ Unknown: <code>{s['unknown']}</code> | 📭 No reply: <code>{s['no_reply']}</code> | ⚠️ Error: <code>{s['error']}</code>",
            f"➕ Joined: <code>{s['joined']}</code>",
        ]
        if self.by_coin:
            lines += ["", "💰 <b>Earned by coin</b>"]
            for coin, total in sorted(self.by_coin.items()):
                lines.append(f"• {html.escape(coin)}: <code>{total:.6g}</code>")
        if self.by_channel:
            lines += ["", "📢 <b>By channel</b>"]
            for title, d in self.by_channel.items():
                lines.append(f"• {html.escape(title)}: {d['claimed']}/{d['detected']}")
        if self.claim_times:
            avg = sum(self.claim_times) / len(self.claim_times)
            lines += ["", f"⚡ Sent → Result avg: {fmt_ms(avg)} | best: {fmt_ms(min(self.claim_times))}"]
        return "\n".join(lines)

    async def on_stats_cmd(self, event):
        await self.send_log(self.summary_text())

    async def process_message(self, msg, source, seen_ts):
        if not msg or not msg.id:
            return

        key = (msg.chat_id, msg.id)
        if key in self.processed_posts:
            return

        payload = self.extract_payload(msg)
        if not payload:
            return
        self.processed_posts.add(key)

        amount, coin, usd = parse_reward(msg)
        title = self.titles.get(msg.chat_id) or getattr(msg.chat, "title", None) or str(msg.chat_id)

        info = {
            "payload": payload,
            "title": title,
            "msg_id": msg.id,
            "source": source,
            "post_dt": msg.date,
            "seen_ts": seen_ts,
            "amount": amount,
            "coin": coin,
            "usd": usd,
        }
        await self.fire_claim(info)

    async def on_new_post(self, event):
        self.spawn(self.process_message(event.message, "push", time.time()))

    async def on_edit_post(self, event):
        self.spawn(self.process_message(event.message, "push (edit)", time.time()))

    async def keep_online(self):
        while True:
            try:
                await self.client(UpdateStatusRequest(offline=False))
            except FloodWaitError as err:
                await asyncio.sleep(err.seconds)
            except Exception:
                pass
            await asyncio.sleep(ONLINE_INTERVAL)

    async def self_ping(self):
        url = os.environ.get("RENDER_EXTERNAL_URL")
        if not url:
            return
        loop = asyncio.get_running_loop()
        while True:
            await asyncio.sleep(PING_INTERVAL)
            try:
                await loop.run_in_executor(None, fetch_url, url)
            except Exception as err:
                print(f"[!] Self-ping failed: {err}")

    async def fast_channel_tracker(self, channel_name, stagger_delay):
        await asyncio.sleep(stagger_delay)
        entity = self.channel_entities.get(channel_name)
        if not entity:
            return

        last_id = 0
        while last_id == 0:
            try:
                msgs = await self.client.get_messages(entity, limit=1)
                if msgs:
                    last_id = msgs[0].id
                else:
                    break
            except FloodWaitError as err:
                await asyncio.sleep(err.seconds + 1)
            except Exception as err:
                print(f"[!] Tracker init error ({channel_name}): {err}")
                await asyncio.sleep(2)

        while True:
            await asyncio.sleep(POLL_INTERVAL)
            try:
                msgs = await self.client.get_messages(entity, limit=1)
                if not msgs:
                    continue
                latest = msgs[0]
                if latest.id > last_id:
                    last_id = latest.id
                    self.spawn(self.process_message(latest, "tracker", time.time()))
            except FloodWaitError as err:
                await asyncio.sleep(err.seconds + 1)
            except Exception:
                await asyncio.sleep(1)

    async def warm_up(self):
        if any(isinstance(t, int) for t in TARGET_CHANNELS):
            try:
                await self.client.get_dialogs()
            except Exception:
                pass

        for target in TARGET_CHANNELS:
            try:
                entity = await self.client.get_entity(target)
                self.titles[utils.get_peer_id(entity)] = getattr(entity, "title", str(target))
                self.channel_entities[target] = await self.client.get_input_entity(entity)
                if JOIN_TARGETS:
                    try:
                        await self.client(JoinChannelRequest(self.channel_entities[target]))
                    except Exception:
                        pass
                print(f"[+] Loaded channel: {target}")
            except Exception as err:
                print(f"[-] Could not resolve channel '{target}': {err}")

        try:
            self.bot_entity = await self.client.get_input_entity(DEFAULT_BOT)
            print(f"[+] Loaded bot: @{DEFAULT_BOT}")
        except Exception as err:
            print(f"[-] Could not resolve bot: {err}")

    async def start(self):
        await self.client.connect()
        if not await self.client.is_user_authorized():
            print("[-] Invalid session.")
            return

        me = await self.client.get_me()
        print(f"[+] Authorized as: {me.first_name} (@{me.username})")

        await self.warm_up()

        watch = list(self.channel_entities.values())
        if not watch:
            print("[-] No channels resolved, stopping.")
            return

        self.client.add_event_handler(self.on_new_post, events.NewMessage(chats=watch))
        self.client.add_event_handler(self.on_edit_post, events.MessageEdited(chats=watch))
        self.client.add_event_handler(self.on_bot_msg, events.NewMessage(chats=DEFAULT_BOT, incoming=True))
        self.client.add_event_handler(self.on_bot_msg, events.MessageEdited(chats=DEFAULT_BOT, incoming=True))
        self.client.add_event_handler(
            self.on_stats_cmd,
            events.NewMessage(chats="me", outgoing=True, pattern=r"(?i)^/?stats$"),
        )

        for index, target in enumerate(self.channel_entities):
            self.spawn(self.fast_channel_tracker(target, stagger_delay=index * 0.2))

        self.spawn(self.keep_online())
        if SELF_PING:
            self.spawn(self.self_ping())

        names = ", ".join(str(t) for t in self.channel_entities)
        print(f"\n[🔥 READY] Watching {len(watch)} channels: {names}")
        await self.send_log(
            f"⚡ <b>xRocket Sniper Running</b>\n"
            f"👤 User: <b>{html.escape(me.first_name or '')}</b>\n"
            f"🎯 Watching: <code>{html.escape(names)}</code>\n"
            f"⏱ Engine: Push + Fast Tracker ({POLL_INTERVAL}s)\n"
            f"📊 Send <code>stats</code> to Saved Messages for a summary"
        )
        await self.client.run_until_disconnected()


def validate_config():
    required = {
        "API_ID": API_ID,
        "API_HASH": API_HASH,
        "SESSION_STRING": SESSION_STRING,
        "TARGET_CHANNELS": TARGET_CHANNELS,
    }
    missing = [name for name, value in required.items() if not value]
    if missing:
        print(f"[-] Missing environment variables: {', '.join(missing)}")
        sys.exit(1)


if __name__ == "__main__":
    validate_config()
    threading.Thread(target=run_flask, daemon=True).start()
    sniper = XRocketSniper(SESSION_STRING, API_ID, API_HASH)
    asyncio.run(sniper.start())
