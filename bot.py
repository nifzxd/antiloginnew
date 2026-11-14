from __future__ import annotations

import dns.resolver
import dns.asyncresolver

dns.resolver.default_resolver = dns.resolver.Resolver(configure=False)
dns.resolver.default_resolver.nameservers = ['8.8.8.8', '1.1.1.1']

dns.asyncresolver.default_resolver = dns.asyncresolver.Resolver(configure=False)
dns.asyncresolver.default_resolver.nameservers = ['8.8.8.8', '1.1.1.1']

import math
import asyncio
import dataclasses
import html
import json
import io
import logging
import re
import secrets
import time
import uuid
import weakref
from contextlib import suppress
from datetime import datetime, timezone, timedelta
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Optional

import qrcode
from telethon import TelegramClient, events, functions
from telethon.tl import types
from telethon.errors import (
    AuthKeyError,
    FloodWaitError,
    PasswordHashInvalidError,
    PhoneCodeExpiredError,
    PhoneCodeInvalidError,
    PhoneNumberInvalidError,
    SessionPasswordNeededError,
    UserDeactivatedBanError,
    UserDeactivatedError,
)
from telethon.sessions import StringSession

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest, TimedOut, NetworkError, RetryAfter
from telegram.ext import (
    AIORateLimiter,
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)
from telegram.request import HTTPXRequest

from licenses import (
    LicenseDatabase,
    LicenseRecord,
    generate_key,
    normalize_key,
    mask_key,
    hash_key,
    LICENSE_STATUS_ACTIVE,
    LICENSE_STATUS_EXPIRED,
    LICENSE_STATUS_REVOKED,
    LICENSE_STATUS_LIFETIME,
)


CONFIG_FILE = "config.json"

REDEEM_MAX_ATTEMPTS = 5
REDEEM_WINDOW_SECONDS = 600
REDEEM_ALERT_THRESHOLD = 3


def _utcnow() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None)


PHONE_REGEX = re.compile(r"^(?:\+\d{7,15}|\+id\d+)$")
CODE_REGEX = re.compile(r"^\d{4,7}$")

OTP_CODE_KEYWORD_RE = re.compile(
    r"(?i)(?:login code|kode|verifikasi|verification code|code)[^\d]{0,30}(\d{5,6})"
)
OTP_CODE_ANY_RE = re.compile(r"\b\d{5,6}\b")

TELEGRAM_SERVICE_ID = 777000
QR_MAX_REFRESHES = 6
HEALTH_CHECK_INTERVAL_SECONDS = 300
USER_SESSION_SWEEP_INTERVAL = 3600
USER_SESSION_IDLE_TIMEOUT = 3600
STEP_TIMEOUT_SECONDS = 900
ACCOUNTS_PER_PAGE = 10
OTP_SESSION_SWEEP_DELAY_SECONDS = 4
ADD_COOLDOWN_SECONDS = 120
UI_CACHE_TTL_SECONDS = 1800
INVALID_SESSION_ERRORS = (
    AuthKeyError,
    UserDeactivatedError,
    UserDeactivatedBanError)


def _extract_otp_code(text: str) -> Optional[str]:
    if not text:
        return None
    m = OTP_CODE_KEYWORD_RE.search(text)
    if m:
        return m.group(1)
    candidates = OTP_CODE_ANY_RE.findall(text)
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        logger.warning(
            "OTP message ambiguous (%d candidates), skipping: %r",
            len(candidates), text[:200],
        )
    return None


class ConsoleFormatter(logging.Formatter):
    COLORS = {
        logging.DEBUG: "\033[90m",
        logging.INFO: "\033[36m",
        logging.WARNING: "\033[33m",
        logging.ERROR: "\033[31m",
        logging.CRITICAL: "\033[41m",
    }
    RESET = "\033[0m"
    GREY = "\033[90m"

    def format(self, record):
        color = self.COLORS.get(record.levelno, "")
        time_str = self.formatTime(record, "%H:%M:%S")
        level = f"{color}{record.levelname:<8}{self.RESET}"
        return f"{self.GREY}{time_str}{self.RESET}  {level}  {record.getMessage()}"


def setup_logging() -> logging.Logger:

    console_handler = logging.StreamHandler()
    console_handler.setFormatter(ConsoleFormatter())

    logging.basicConfig(
        level=logging.INFO,
        handlers=[console_handler],
        force=True)
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("telethon").setLevel(logging.WARNING)
    
    audit = logging.getLogger("audit")
    audit.setLevel(logging.INFO)
    audit.propagate = True

    return logging.getLogger("anti_login")


logger = setup_logging()
audit_logger = logging.getLogger("audit")


@dataclasses.dataclass(frozen=True)
class Config:
    api_id: int
    api_hash: str
    bot_token: str
    admin_ids: frozenset
    license_salt: str
    mongo_uri: str
    db_name: str


def _to_int_set(values) -> frozenset:
    result = set()
    for value in values or []:
        if isinstance(value, bool):
            logger.warning("Ignoring bool id in config.json: %r", value)
            continue
        try:
            result.add(int(value))
        except (TypeError, ValueError):
            logger.warning("Ignoring invalid id in config.json: %r", value)
    return frozenset(result)


def load_config(path: Path) -> Optional[Config]:
    if not path.exists():
        sample = {
            "api_id": 123456,
            "api_hash": "your_hash",
            "bot_token": "your_token",
            "admin_ids": [123456789],
            "mongo_uri": "mongodb://localhost:27017",
            "db_name": "anti_login_bot"
        }
        path.write_text(json.dumps(sample, indent=2))
        logger.warning(
            "%s not found. A sample has been created — fill it in and restart.", path)
        return None

    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as e:
        logger.error("Failed to read %s: %s", path, e)
        return None

    if not isinstance(raw, dict):
        logger.error("config.json must be a JSON object")
        return None

    raw_api_id = raw.get("api_id")
    if isinstance(raw_api_id, bool):
        logger.error("api_id must be an integer, not bool")
        return None
    try:
        api_id = int(raw_api_id)
    except (TypeError, ValueError):
        logger.error("api_id must be an integer, got %r", raw_api_id)
        return None
    if not (1 <= api_id <= 10_000_000_000):
        logger.error("api_id out of plausible range: %s", api_id)
        return None

    api_hash = raw.get("api_hash")
    if not isinstance(api_hash, str) or not re.fullmatch(r"[0-9a-fA-F]{32}", api_hash):
        logger.error("api_hash must be a 32-char hex string")
        return None
    if "your_hash" in api_hash.lower():
        logger.error("api_hash still sample value — change it first")
        return None

    bot_token = raw.get("bot_token")
    if not isinstance(bot_token, str) or not re.fullmatch(r"\d+:[A-Za-z0-9_-]{30,50}", bot_token):
        logger.error("bot_token format invalid (expected '<id>:<secret>')")
        return None
    if "your_token" in bot_token.lower():
        logger.error("bot_token still sample value — change it first")
        return None

    salt = raw.get("license_salt")
    if not isinstance(salt, str) or not re.fullmatch(r"[0-9a-fA-F]{32}", salt or ""):
        salt = secrets.token_hex(16)
        raw["license_salt"] = salt
        try:
            path.write_text(
                json.dumps(raw, indent=2, ensure_ascii=False), encoding="utf-8")
            logger.info("Generated new license_salt and saved to config.json")
        except OSError as e:
            logger.error("Failed to persist license_salt: %s", e)

    mongo_uri = raw.get("mongo_uri")
    if not isinstance(mongo_uri, str) or not mongo_uri.strip():
        logger.warning(
            "mongo_uri is missing or empty in config.json. Falling back to localhost.")
        mongo_uri = "mongodb://localhost:27017"

    db_name = raw.get("db_name")
    if not isinstance(db_name, str) or not db_name.strip():
        db_name = "anti_login_bot"

    return Config(
        api_id=api_id,
        api_hash=api_hash,
        bot_token=bot_token,
        admin_ids=_to_int_set(raw.get("admin_ids")),
        license_salt=salt,
        mongo_uri=mongo_uri,
        db_name=db_name,
    )


def normalize_phone(raw: str) -> str:
    if raw.startswith("+id"):
        return raw
    return "+" + re.sub(r"\D", "", raw)


@dataclasses.dataclass
class AccountRecord:
    phone: str
    session_str: str
    anti_login: bool = False
    owner_id: Optional[int] = None
    created_at: str = dataclasses.field(default_factory=lambda: _utcnow().isoformat())
    updated_at: str = dataclasses.field(default_factory=lambda: _utcnow().isoformat())
    invalidated_codes: int = 0
    whitelisted_sessions: list = dataclasses.field(default_factory=list)
    whitelist_initialized: bool = False

    def touch(self):
        self.updated_at = _utcnow().isoformat()

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)

    @staticmethod
    def from_dict(phone: str, data: dict) -> "AccountRecord":
        oid = data.get("owner_id")
        if oid is not None:
            try:
                oid = int(oid)
            except (TypeError, ValueError):
                oid = None
        return AccountRecord(
            phone=phone,
            session_str=str(data["session_str"]),
            anti_login=bool(data.get("anti_login", False)),
            owner_id=oid,
            created_at=str(data.get("created_at") or _utcnow().isoformat()),
            updated_at=str(data.get("updated_at") or _utcnow().isoformat()),
            invalidated_codes=int(data.get("invalidated_codes", 0) or 0),
            whitelisted_sessions=list(data.get("whitelisted_sessions", []) or []),
            whitelist_initialized=bool(data.get("whitelist_initialized", False)),
        )


def _format_session(auth, prefix: str = "") -> str:
    created = auth.date_created.strftime("%Y-%m-%d %H:%M") if auth.date_created else "?"
    return (
        f"{prefix}<b>{html.escape(auth.device_model or '?')}</b> "
        f"({html.escape(auth.platform or '?')})\n"
        f"   App: {html.escape(auth.app_name or '?')} {html.escape(auth.app_version or '')}\n"
        f"   Location: {html.escape(auth.country or '?')}, {html.escape(auth.region or '?')}\n"
        f"   IP: {html.escape(auth.ip or '?')}\n"
        f"   Created: {created}\n"
    )


class AccountDatabase:
    def __init__(self, mongo_uri: str, db_name: str = "anti_login_bot"):
        from pymongo import AsyncMongoClient
        self.client = AsyncMongoClient(mongo_uri)
        self.db = self.client[db_name]
        self.collection = self.db["accounts"]

    async def load(self) -> list:
        await self.collection.create_index("phone", unique=True)
        await self.collection.create_index("owner_id")
        return []

    async def get(self, phone: str) -> Optional[AccountRecord]:
        data = await self.collection.find_one({"phone": phone}, {"_id": 0})
        if data:
            return AccountRecord.from_dict(phone, data)
        return None

    async def all(self) -> dict:
        cursor = self.collection.find({}, {"_id": 0})
        records = {}
        async for data in cursor:
            phone = data.get("phone")
            if phone:
                records[phone] = AccountRecord.from_dict(phone, data)
        return records

    async def contains(self, phone: str) -> bool:
        count = await self.collection.count_documents({"phone": phone}, limit=1)
        return count > 0

    async def upsert(self, record: AccountRecord):
        record.touch()
        await self.collection.update_one(
            {"phone": record.phone},
            {"$set": record.to_dict()},
            upsert=True
        )

    async def mutate(self, phone: str, fn) -> Optional[AccountRecord]:
        record = await self.get(phone)
        if record is None:
            return None
        fn(record)
        await self.upsert(record)
        return record

    async def remove(self, phone: str) -> bool:
        result = await self.collection.delete_one({"phone": phone})
        return result.deleted_count > 0

    async def assign_owner_batch(self, phone_owner_map: dict):
        for phone, owner in phone_owner_map.items():
            await self.collection.update_one(
                {"phone": phone, "owner_id": None},
                {"$set": {"owner_id": owner, "updated_at": _utcnow().isoformat()}}
            )


class SessionManager:
    def __init__(self, config: Config, database: AccountDatabase):
        self.config = config
        self.database = database
        self.clients: dict[str, TelegramClient] = {}
        self.tasks: list[asyncio.Task] = []
        self.bot_app: Optional[Application] = None
        self._reconnect_delays: dict[str, float] = {}
        self._reconnect_locks: dict[str, asyncio.Lock] = {}
        self._guarded_clients: weakref.WeakSet = weakref.WeakSet()
        self._ui_sessions: dict[str, tuple] = {}

    async def is_protected(self, phone: str) -> bool:
        record = await self.database.get(phone)
        return bool(record and record.anti_login)

    async def phones(self) -> list:
        return list((await self.database.all()).keys())

    def track(self, task: asyncio.Task):
        self.tasks[:] = [t for t in self.tasks if not t.done()]
        self.tasks.append(task)

    async def load_all(self):
        rejected = await self.database.load()
        for phone in rejected:
            logger.info("Discarded unrecoverable account record: %s", phone)

        default_owner = min(self.config.admin_ids) if self.config.admin_ids else None
        if default_owner is not None:
            legacy = {
                p: default_owner
                for p, r in (await self.database.all()).items()
                if r.owner_id is None
            }
            if legacy:
                await self.database.assign_owner_batch(legacy)
                logger.info("Migrated %d legacy accounts to owner %d", len(legacy), default_owner)
                audit_logger.info("migration_owner_assigned count=%d admin_id=%d", len(legacy), default_owner)

        sem = asyncio.Semaphore(5)

        async def connect(phone: str, record: AccountRecord):
            async with sem:
                await self._connect_existing(phone, record)

        records = list((await self.database.all()).items())
        if records:
            await asyncio.gather(*(connect(p, r) for p, r in records))

    async def _connect_existing(self, phone: str, record: AccountRecord):
        try:
            session = StringSession(record.session_str)
        except (ValueError, TypeError) as e:
            logger.error("Corrupt session_str for %s (%s). Removing.", phone, e)
            await self.database.remove(phone)
            return

        client = TelegramClient(session, self.config.api_id, self.config.api_hash)
        try:
            await client.connect()
            if not await client.is_user_authorized():
                raise AuthKeyError("session no longer authorized")
            me = await client.get_me()
            if me is None:
                raise AuthKeyError("get_me returned None — session likely invalid")
            self.clients[phone] = client
            try:
                self._setup_otp_guard(phone, client)
                self.track(asyncio.create_task(self._supervise_client(phone, client)))
                await self._ensure_whitelist_initialized(phone, client)
            except Exception:
                self.clients.pop(phone, None)
                raise
            logger.info("Account loaded: %s (%s)", phone, me.first_name)
        except INVALID_SESSION_ERRORS as e:
            logger.error("Session for %s is no longer valid (%s). Removing from database.", phone, e)
            with suppress(Exception):
                await client.disconnect()
            self.clients.pop(phone, None)
            await self.database.remove(phone)
            await notify_admins_session_removed(self.bot_app, self.config, phone, str(e))
        except Exception as e:
            self.clients.pop(phone, None)
            logger.error("Failed to load account %s: %s. Will retry via health check.", phone, e)
            with suppress(Exception):
                await client.disconnect()

    async def _supervise_client(self, phone: str, client: TelegramClient):
        try:
            await client.run_until_disconnected()
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning("Client task for %s ended unexpectedly: %s", phone, e)

    async def add_account(self, phone: str, client: TelegramClient, owner_id: Optional[int] = None) -> bool:
        if await self.database.contains(phone):
            return False
        record = AccountRecord(
            phone=phone,
            session_str=client.session.save(),
            anti_login=False,
            owner_id=owner_id,
        )
        try:
            await self.database.upsert(record)
            self.clients[phone] = client
            try:
                self._setup_otp_guard(phone, client)
                self.track(asyncio.create_task(self._supervise_client(phone, client)))
                await self._ensure_whitelist_initialized(phone, client)
            except Exception:
                self.clients.pop(phone, None)
                raise
        except Exception as e:
            logger.error("add_account failed for %s: %s", phone, e)
            self.clients.pop(phone, None)
            with suppress(Exception):
                await self.database.remove(phone)
            raise
        logger.info("Account added: %s (owner=%s)", phone, owner_id)
        audit_logger.info("account_added phone=%s owner=%s", phone, owner_id)
        return True

    async def remove_account(self, phone: str) -> bool:
        client = self.clients.get(phone)
        logged_out = False
        if client:
            for attempt in range(3):
                try:
                    await client(functions.auth.LogOutRequest())
                    logged_out = True
                    audit_logger.info("account_logout phone=%s attempt=%d", phone, attempt + 1)
                    break
                except Exception as e:
                    if attempt < 2:
                        logger.info("Logout retry for %s (attempt %d): %s", phone, attempt + 2, e)
                        await asyncio.sleep(2 ** attempt)
                        continue
                    logger.error("Logout FAILED for %s after retries: %s", phone, e)
                    await _broadcast_to_admins(
                        self.bot_app, self.config,
                        f"⚠️ <b>Logout fail</b> for <code>{html.escape(phone)}</code>.\n"
                        f"Session may still be active on Telegram. Try <b>Remove Account</b> again later.",
                    )
                    with suppress(Exception):
                        await client.disconnect()
                    return False
            self.clients.pop(phone, None)
            with suppress(Exception):
                await client.disconnect()

        removed = await self.database.remove(phone)
        if removed:
            audit_logger.info("account_removed phone=%s logged_out=%s", phone, logged_out)
            logger.info("Removed account %s (logged_out=%s,)", phone, logged_out)
        return removed

    async def toggle_anti_login(self, phone: str) -> bool:
        def _toggle(r: AccountRecord):
            r.anti_login = not r.anti_login

        record = await self.database.mutate(phone, _toggle)
        if record is None:
            return False
        logger.info("Anti-Login %s -> %s", phone, "ENABLED" if record.anti_login else "DISABLED")
        audit_logger.info("anti_login_toggle phone=%s state=%s", phone, record.anti_login)
        return True

    async def reset_baseline(self, phone: str) -> bool:
        client = self.clients.get(phone)
        if not client:
            return False

        def _reset(r: AccountRecord):
            r.whitelist_initialized = False
            r.whitelisted_sessions = []

        await self.database.mutate(phone, _reset)
        ok = await self._ensure_whitelist_initialized(phone, client)
        audit_logger.info("baseline_reset phone=%s ok=%s", phone, ok)
        return ok

    async def reconnect(self, phone: str) -> bool:
        lock = self._reconnect_locks.setdefault(phone, asyncio.Lock())
        async with lock:
            record = await self.database.get(phone)
            if not record:
                return False

            existing = self.clients.get(phone)
            if existing and existing.is_connected():
                try:
                    if await existing.is_user_authorized():
                        return True
                except Exception:
                    pass

            old_client = self.clients.pop(phone, None)
            if old_client:
                with suppress(Exception):
                    await old_client.disconnect()

            try:
                session = StringSession(record.session_str)
            except (ValueError, TypeError) as e:
                logger.error("Corrupt session_str for %s during reconnect (%s). Removing.", phone, e)
                await self.database.remove(phone)
                return False

            client = TelegramClient(session, self.config.api_id, self.config.api_hash)
            try:
                await client.connect()
                if not await client.is_user_authorized():
                    raise AuthKeyError("session no longer authorized")
                me = await client.get_me()
                if me is None:
                    raise AuthKeyError("get_me returned None — session likely invalid")
                self.clients[phone] = client
                try:
                    self._setup_otp_guard(phone, client)
                    self.track(asyncio.create_task(self._supervise_client(phone, client)))
                    await self._ensure_whitelist_initialized(phone, client)
                except Exception:
                    self.clients.pop(phone, None)
                    raise
                self._reconnect_delays.pop(phone, None)
                logger.info("Reconnected: %s", phone)
                return True
            except INVALID_SESSION_ERRORS as e:
                logger.error("Session for %s is invalid during reconnect (%s). Removing.", phone, e)
                with suppress(Exception):
                    await client.disconnect()
                self.clients.pop(phone, None)
                await self.database.remove(phone)
                await notify_admins_session_removed(self.bot_app, self.config, phone, str(e))
                return False
            except FloodWaitError as e:
                logger.warning("Reconnect for %s hit flood wait: %ds", phone, e.seconds)
                with suppress(Exception):
                    await client.disconnect()
                self._reconnect_delays[phone] = time.monotonic() + e.seconds
                return False
            except Exception as e:
                logger.error("Failed to reconnect %s: %s", phone, e)
                with suppress(Exception):
                    await client.disconnect()
                return False

    async def reconnect_all(self):
        for phone in await self.phones():
            delay_until = self._reconnect_delays.get(phone)
            if delay_until and time.monotonic() < delay_until:
                continue
            await self.reconnect(phone)

    async def health_check_loop(self, interval_seconds: int = HEALTH_CHECK_INTERVAL_SECONDS):
        while True:
            await asyncio.sleep(interval_seconds)
            for phone in await self.phones():
                with suppress(Exception):
                    await self._health_check_one(phone)

    async def _health_check_one(self, phone: str):
        record = await self.database.get(phone)
        if not record:
            return
        delay_until = self._reconnect_delays.get(phone)
        if delay_until and time.monotonic() < delay_until:
            return

        client = self.clients.get(phone)
        if client and client.is_connected():
            try:
                if not await client.is_user_authorized():
                    raise AuthKeyError("session no longer authorized")
                with suppress(Exception):
                    await self.check_sessions(phone, source="health_check")
                return
            except INVALID_SESSION_ERRORS as e:
                logger.error("Detected invalid session for %s (%s). Removing.", phone, e)
                with suppress(Exception):
                    await client.disconnect()
                self.clients.pop(phone, None)
                await self.database.remove(phone)
                await notify_admins_session_removed(self.bot_app, self.config, phone, str(e))
                return
            except Exception:
                return

        logger.info("Client for %s appears disconnected. Attempting reconnect.", phone)
        await self.reconnect(phone)

    def _setup_otp_guard(self, phone: str, client: TelegramClient):
        if client in self._guarded_clients:
            return
        self._guarded_clients.add(client)

        @client.on(events.NewMessage(from_users=[TELEGRAM_SERVICE_ID]))
        async def handle_otp(event):
            try:
                await self._handle_otp_event(phone, event)
            except Exception as e:
                logger.error("Error while handling OTP event for %s: %s", phone, e)

    async def _handle_otp_event(self, phone: str, event):
        if not await self.is_protected(phone):
            return
        code = _extract_otp_code(event.message.text or "")
        if not code:
            return
        client = self.clients.get(phone)
        if not client:
            return
        try:
            await client(functions.account.InvalidateSignInCodesRequest(codes=[code]))
            logger.warning("Login code %s for %s was invalidated.", code, phone)
            audit_logger.warning("otp_invalidated phone=%s code=%s", phone, code)
        except Exception as e:
            logger.error("Failed to invalidate code for %s: %s", phone, e)
            return

        def _inc(r: AccountRecord):
            r.invalidated_codes += 1

        record = await self.database.mutate(phone, _inc)
        if record is None:
            return

        self.track(asyncio.create_task(
            self._delayed_session_sweep(phone, delay=OTP_SESSION_SWEEP_DELAY_SECONDS, source="otp_event")
        ))

        await notify_admins_login_attempt(self.bot_app, self.config, phone)

    def _whitelist_session(self, record: AccountRecord, auth, source: str = "manual") -> None:
        entry = {
            "hash": auth.hash,
            "device_model": auth.device_model,
            "platform": auth.platform,
            "app_name": auth.app_name,
            "app_version": auth.app_version,
            "country": auth.country,
            "region": auth.region,
            "ip": auth.ip,
            "date_created": auth.date_created.isoformat() if auth.date_created else None,
            "trusted_at": _utcnow().isoformat(),
            "source": source,
        }
        record.whitelisted_sessions = [
            e for e in record.whitelisted_sessions if e.get("hash") != auth.hash
        ]
        record.whitelisted_sessions.append(entry)

    def _is_trusted(self, record: AccountRecord, auth) -> bool:
        if auth.current:
            return True
        return any(e.get("hash") == auth.hash for e in record.whitelisted_sessions)

    async def _kill_session(self, client, auth, phone: str) -> bool:
        try:
            await client(functions.account.ResetAuthorizationRequest(hash=auth.hash))
            logger.warning(
                "Killed session for %s: %s / %s (%s)",
                phone, auth.device_model, auth.platform, auth.country,
            )
            audit_logger.warning(
                "session_killed phone=%s device=%s platform=%s ip=%s",
                phone, auth.device_model, auth.platform, auth.ip,
            )
            return True
        except Exception as e:
            logger.info("Could not kill session for %s (hash=%s): %s", phone, auth.hash, e)
            return False

    async def _ensure_whitelist_initialized(self, phone: str, client: TelegramClient) -> bool:
        record = await self.database.get(phone)
        if not record:
            return False
        if record.whitelist_initialized:
            return True
        try:
            result = await client(functions.account.GetAuthorizationsRequest())
        except Exception as e:
            logger.error("Failed to fetch authorizations for baseline %s: %s", phone, e)
            return False

        def _apply(r: AccountRecord):
            for auth in result.authorizations:
                self._whitelist_session(r, auth, source="baseline")
            r.whitelist_initialized = True

        record = await self.database.mutate(phone, _apply)
        if record is None:
            return False
        logger.info("Baseline whitelist for %s: %d session(s) trusted", phone, len(result.authorizations))
        audit_logger.info("baseline_init phone=%s count=%d", phone, len(result.authorizations))
        return True

    async def check_sessions(self, phone: str, source: str) -> list:
        record = await self.database.get(phone)
        client = self.clients.get(phone)
        if not record or not client:
            return []

        if not record.whitelist_initialized:
            ok = await self._ensure_whitelist_initialized(phone, client)
            if not ok:
                logger.warning(
                    "Skipping session sweep for %s (%s): baseline not initialized", phone, source,
                )
                await _broadcast_to_admins(
                    self.bot_app, self.config,
                    f"⚠️ <b>Baseline not ready</b> for <code>{html.escape(phone)}</code>\n"
                    f"Anti-login can't sweep session (<i>{html.escape(source)}</i>).\n"
                    f"Use the button <b>Reset Baseline</b>.",
                )
                return []
            record = await self.database.get(phone)
            if not record:
                return []

        try:
            result = await client(functions.account.GetAuthorizationsRequest())
        except Exception as e:
            logger.error("Failed to fetch authorizations for %s: %s", phone, e)
            return []

        to_kill = []
        for auth in result.authorizations:
            if self._is_trusted(record, auth):
                continue
            if auth.current:
                logger.error("Refusing to kill current session for %s", phone)
                continue
            to_kill.append(auth)

        killed = []
        for auth in to_kill:
            if await self._kill_session(client, auth, phone):
                killed.append(auth)

        if killed:
            def _apply(r: AccountRecord):
                killed_hashes = {a.hash for a in killed}
                r.whitelisted_sessions = [
                    e for e in r.whitelisted_sessions if e.get("hash") not in killed_hashes
                ]
            await self.database.mutate(phone, _apply)
            await notify_admins_session_killed(self.bot_app, self.config, phone, killed, source)

        return killed

    async def _delayed_session_sweep(self, phone: str, delay: float, source: str):
        await asyncio.sleep(delay)
        with suppress(Exception):
            await self.check_sessions(phone, source=source)

    async def shutdown(self):
        for task in self.tasks:
            task.cancel()
        if self.tasks:
            await asyncio.gather(*self.tasks, return_exceptions=True)
        self.tasks.clear()

        for client in list(self.clients.values()):
            with suppress(Exception):
                await client.disconnect()
        self.clients.clear()

        try:
            if hasattr(self, 'database') and hasattr(self.database, 'client'):
                await self.database.client.close()
            if _license_db and hasattr(_license_db, 'client'):
                await _license_db.client.close()
        except Exception as e:
            logger.debug(f"Failed to close MongoDB connection cleanly: {e}")

        logger.info("All account connections closed and MongoDB disconnected.")


async def _broadcast_to_admins(bot_app: Optional[Application], config: Config, text: str, markup=None):
    if not bot_app or not config.admin_ids:
        return

    async def send(aid):
        with suppress(Exception):
            await bot_app.bot.send_message(
                aid, text, parse_mode=ParseMode.HTML, reply_markup=markup,
            )

    await asyncio.gather(*(send(a) for a in config.admin_ids))


async def notify_admins_login_attempt(bot_app: Optional[Application], config: Config, phone: str):
    text = (
        "🚨 <b>Login Attempt Detected</b>\n"
        f"Account: <code>{html.escape(phone)}</code>\n"
        f"Time: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
        "The login code was automatically invalidated."
    )
    await _broadcast_to_admins(bot_app, config, text)


async def notify_admins_session_removed(bot_app: Optional[Application], config: Config, phone: str, reason: str):
    text = (
        "🧹 <b>Session Removed</b>\n"
        f"Account: <code>{html.escape(phone)}</code>\n"
        f"Reason: {html.escape(reason)}\n"
        "This account was disconnected and cleaned up from the database. Re-add it if needed."
    )
    await _broadcast_to_admins(bot_app, config, text)


async def notify_admins_session_killed(
    bot_app: Optional[Application], config: Config,
    phone: str, killed_sessions, source: str,
):
    if not bot_app or not config.admin_ids:
        return

    lines = [
        "🔪 <b>Unauthorized Session Killed</b>",
        f"Account: <code>{html.escape(phone)}</code>",
        f"Trigger: <i>{html.escape(source)}</i>",
        "",
    ]
    for auth in killed_sessions:
        lines.append(_format_session(auth, prefix="• "))

    await _broadcast_to_admins(bot_app, config, "\n".join(lines))


_config: Optional[Config] = None
_session_manager: Optional[SessionManager] = None
_license_db: Optional[LicenseDatabase] = None
user_sessions: dict = {}
_add_cooldown: dict[int, float] = {}
_redeem_attempts: dict[int, list[float]] = {}
_pending_lic_gen: dict[int, dict] = {}


# ============================================================================
# Access control
# ============================================================================

def is_super_admin(user_id: int) -> bool:
    return bool(_config) and user_id in _config.admin_ids


async def get_user_license(user_id: int) -> Optional[LicenseRecord]:
    if _license_db is None:
        return None
    return await _license_db.get_by_owner(user_id)


async def is_authorized(user_id: int) -> bool:
    if is_super_admin(user_id):
        return True
    lic = await get_user_license(user_id)
    return bool(lic and lic.is_usable())


async def can_manage_account(user_id: int, phone: str) -> bool:
    if is_super_admin(user_id):
        return True
    lic = await get_user_license(user_id)
    if not lic or not lic.is_usable():
        return False
    if not _session_manager:
        return False
    rec = await _session_manager.database.get(phone)
    return bool(rec and rec.owner_id == user_id)


async def count_owned_accounts(user_id: int) -> int:
    if not _session_manager:
        return 0
    all_accs = await _session_manager.database.all()
    return sum(1 for r in all_accs.values() if r.owner_id == user_id)


async def _check_license_quota(user_id: int) -> Optional[str]:
    if is_super_admin(user_id):
        return None
    lic = await get_user_license(user_id)
    if not lic or not lic.is_usable():
        return "Your license is not active."
    used = await count_owned_accounts(user_id)
    if used >= lic.max_accounts:
        return f"Quota full ({used}/{lic.max_accounts}). Delete old accounts or upgrade your license."
    return None


def _check_add_cooldown(user_id: int) -> Optional[str]:
    last = _add_cooldown.get(user_id, 0.0)
    delta = time.monotonic() - last
    if delta < ADD_COOLDOWN_SECONDS:
        return f"⏳ Wait {int(ADD_COOLDOWN_SECONDS - delta + 1)} seconds before adding another account."
    return None


def _bump_control_message(chat_id: int, old_id: int, new_id: int):
    for sess in user_sessions.values():
        if sess.get("chat_id") == chat_id and sess.get("control_msg_id") == old_id:
            sess["control_msg_id"] = new_id


async def _safe_answer(query, text: Optional[str] = None, show_alert: bool = False):
    if query is None:
        return
    if getattr(query, "_safe_answered", False):
        return
    try:
        query._safe_answered = True
    except AttributeError:
        pass
    try:
        await query.answer(text=text, show_alert=show_alert)
    except (BadRequest, TimedOut, NetworkError) as e:
        logger.debug("answer() suppressed: %s", e)


def _validate_keyboard(keyboard) -> None:
    if not keyboard:
        return
    for row in keyboard:
        for btn in row:
            cb = getattr(btn, "callback_data", None)
            if isinstance(cb, str):
                encoded = cb.encode("utf-8")
                if len(encoded) > 64:
                    logger.error(
                        "callback_data exceeds 64 bytes (%d): %r", len(encoded), cb,
                    )


async def render(context, chat_id: int, message_id: int, text: str, keyboard=None) -> int:
    _validate_keyboard(keyboard)
    markup = InlineKeyboardMarkup(keyboard) if keyboard else None
    try:
        await context.bot.edit_message_text(
            chat_id=chat_id,
            message_id=message_id,
            text=text,
            parse_mode=ParseMode.HTML,
            reply_markup=markup,
        )
        return message_id
    except BadRequest as e:
        err = str(e).lower()
        if "message is not modified" in err:
            return message_id
        if "message to edit not found" in err or "message can't be edited" in err:
            logger.info("Control message %s missing; sending fresh message", message_id)
            msg = await context.bot.send_message(
                chat_id, text, parse_mode=ParseMode.HTML, reply_markup=markup,
            )
            _bump_control_message(chat_id, message_id, msg.message_id)
            return msg.message_id
        logger.warning("HTML parse failed, retrying as plain text: %s", e)

    plain = html.unescape(re.sub(r"<[^>]+>", "", text))
    try:
        await context.bot.edit_message_text(
            chat_id=chat_id, message_id=message_id, text=plain, reply_markup=markup,
        )
        return message_id
    except BadRequest as e:
        err = str(e).lower()
        if "message is not modified" in err:
            return message_id
        if "message to edit not found" in err or "message can't be edited" in err:
            msg = await context.bot.send_message(chat_id, plain, reply_markup=markup)
            _bump_control_message(chat_id, message_id, msg.message_id)
            return msg.message_id
        logger.error("Failed to edit message: %s", e)
        return message_id


def main_menu_keyboard(user_id: int):
    if is_super_admin(user_id):
        return [
            [InlineKeyboardButton("➕ Add Account", callback_data="add_acc"),
             InlineKeyboardButton("📋 Account List", callback_data="list_acc")],
            [InlineKeyboardButton("📊 Stats", callback_data="stats"),
             InlineKeyboardButton("🔄 Reconnect All", callback_data="reconnect_all")],
            [InlineKeyboardButton("🛡️ License Manager", callback_data="lic_mgr")],
        ]
    return [
        [InlineKeyboardButton("➕ Add Account", callback_data="add_acc"),
         InlineKeyboardButton("📋 My Accounts", callback_data="list_acc")],
        [InlineKeyboardButton("📊 My Stats", callback_data="stats"),
         InlineKeyboardButton("🔑 My License", callback_data="lic_my")],
    ]


async def show_main_menu(context, chat_id, message_id, user_id):
    await render(
        context, chat_id, message_id,
        "🛡️ <b>Welcome to Anti-Login Bot</b>\n"
        "Securely manage and monitor your protected accounts.\n\n"
        "👨‍💻 Developer: @nifzz",
        main_menu_keyboard(user_id),
    )


def _account_sort_key(kv):
    phone = kv[0]
    return (1 if phone.startswith("+id") else 0, phone)


async def list_accounts_view(context, chat_id, message_id, user_id, page: int = 0, filter_q: str = ""):
    accounts = sorted((await _session_manager.database.all()).items(), key=_account_sort_key)
    if not is_super_admin(user_id):
        accounts = [(p, r) for p, r in accounts if r.owner_id == user_id]
    if filter_q:
        accounts = [(p, r) for p, r in accounts if filter_q in p]

    if not accounts:
        keyboard = [[InlineKeyboardButton("🔙 Back", callback_data="menu")]]
        msg = "📋 <b>Account List</b>\n\nNo accounts" + (
            f" matching <code>{html.escape(filter_q)}</code>." if filter_q else " registered yet."
        )
        await render(context, chat_id, message_id, msg, keyboard)
        return

    total_pages = max(1, (len(accounts) + ACCOUNTS_PER_PAGE - 1) // ACCOUNTS_PER_PAGE)
    page = max(0, min(page, total_pages - 1))
    start = page * ACCOUNTS_PER_PAGE
    end = start + ACCOUNTS_PER_PAGE
    chunk = accounts[start:end]

    keyboard = []
    for phone, record in chunk:
        keyboard.append([
            InlineKeyboardButton(
                f"{'🔒' if record.anti_login else '🔓'} {phone}",
                callback_data=f"acc_{phone}",
            )
        ])

    nav_row = []
    if page > 0:
        nav_row.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"list_acc_{page - 1}"))
    if page < total_pages - 1:
        nav_row.append(InlineKeyboardButton("Next ➡️", callback_data=f"list_acc_{page + 1}"))
    if nav_row:
        keyboard.append(nav_row)
    keyboard.append([InlineKeyboardButton("🔙 Back", callback_data="menu")])

    header = f"📋 <b>Account List</b> (page {page + 1}/{total_pages})"
    if filter_q:
        header += f"\n🔍 Filter: <code>{html.escape(filter_q)}</code>"
    await render(context, chat_id, message_id, header, keyboard)


async def account_detail_view(context, chat_id, message_id, user_id, phone, banner: str = ""):
    if not await can_manage_account(user_id, phone):
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    record = await _session_manager.database.get(phone)
    if not record:
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    status = "🔒 ENABLED" if record.anti_login else "🔓 DISABLED"
    baseline = "✅ ready" if record.whitelist_initialized else "⚠️ not initialized"
    text = (
        f"{html.escape(banner)}📱 <b>{html.escape(phone)}</b>\n"
        f"Anti-Login status: <b>{status}</b>\n"
        f"Codes invalidated so far: {record.invalidated_codes}\n"
        f"Whitelisted sessions: <b>{len(record.whitelisted_sessions)}</b>\n"
        f"Baseline: {baseline}"
    )
    toggle_label = "🔓 Disable" if record.anti_login else "🔒 Enable"
    keyboard = [
        [InlineKeyboardButton(toggle_label, callback_data=f"toggle_{phone}")],
        [InlineKeyboardButton("🔐 Sessions", callback_data=f"sessions_{phone}")],
        [InlineKeyboardButton("♻️ Reset Baseline", callback_data=f"resetbase_{phone}")],
        [InlineKeyboardButton("🗑 Remove Account", callback_data=f"del_{phone}")],
        [InlineKeyboardButton("🔙 Back", callback_data="list_acc")],
    ]
    await render(context, chat_id, message_id, text, keyboard)


async def sessions_view(context, chat_id, message_id, user_id, phone, banner: str = ""):
    if not await can_manage_account(user_id, phone):
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    record = await _session_manager.database.get(phone)
    client = _session_manager.clients.get(phone)
    if not record:
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    if not client:
        await render(
            context, chat_id, message_id,
            f"{banner}⚠️ Client for <code>{html.escape(phone)}</code> is not connected.",
            [[InlineKeyboardButton("🔙 Back", callback_data=f"acc_{phone}")]],
        )
        return

    try:
        result = await client(functions.account.GetAuthorizationsRequest())
    except Exception as e:
        await render(
            context, chat_id, message_id,
            f"{banner}❌ Failed to fetch sessions: {html.escape(str(e))}",
            [[InlineKeyboardButton("🔙 Back", callback_data=f"acc_{phone}")]],
        )
        return

    lines = [f"{banner}🔐 <b>Sessions for {html.escape(phone)}</b>\n"]
    keyboard_rows = []
    for auth in result.authorizations:
        trusted = _session_manager._is_trusted(record, auth)
        tag = "🟢" if trusted else "🔴"
        me_tag = " <i>(bot)</i>" if auth.current else ""
        lines.append(f"{tag}{me_tag}\n{_format_session(auth)}")

        if not auth.current:
            short = uuid.uuid4().hex[:10]
            _session_manager._ui_sessions[short] = (phone, auth.hash, time.monotonic())
            device = auth.device_model or "device"
            row = []
            if not trusted:
                row.append(InlineKeyboardButton(
                    f"✅ Trust {device}",
                    callback_data=f"sess_trust_{short}",
                ))
            row.append(InlineKeyboardButton(
                f"🚪 Logout {device}",
                callback_data=f"revokeconfirm_{short}",
            ))
            keyboard_rows.append(row)

    keyboard_rows.append([InlineKeyboardButton("🔄 Refresh", callback_data=f"sessions_{phone}")])
    keyboard_rows.append([InlineKeyboardButton("🔙 Back", callback_data=f"acc_{phone}")])
    await render(context, chat_id, message_id, "\n".join(lines), keyboard_rows)


async def delete_confirm_view(context, chat_id, message_id, user_id, phone):
    if not await can_manage_account(user_id, phone):
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    if not await _session_manager.database.contains(phone):
        await list_accounts_view(context, chat_id, message_id, user_id)
        return
    keyboard = [
        [
            InlineKeyboardButton("✅ Yes, Remove", callback_data=f"delconfirm_{phone}"),
            InlineKeyboardButton("❌ Cancel", callback_data=f"acc_{phone}"),
        ]
    ]
    await render(
        context, chat_id, message_id,
        f"⚠️ Remove account <code>{html.escape(phone)}</code>?", keyboard,
    )


def cancel_keyboard():
    return [[InlineKeyboardButton("❌ Cancel", callback_data="cancel_add")]]


def add_method_keyboard():
    return [
        [InlineKeyboardButton("📱 Phone Number", callback_data="add_phone")],
        [InlineKeyboardButton("🔲 QR Code", callback_data="add_qr")],
        [InlineKeyboardButton("🔙 Back", callback_data="menu")],
    ]


async def cleanup_session_client(session: dict):
    client = session.get("client")
    if client:
        with suppress(Exception):
            await client.disconnect()


async def cleanup_qr_message(bot, session: dict):
    qr_msg_id = session.get("qr_msg_id")
    if qr_msg_id and bot:
        with suppress(Exception):
            await bot.delete_message(session["chat_id"], qr_msg_id)


async def reset_user_flow(context, user_id: int):
    session = user_sessions.pop(user_id, None)
    if not session:
        return
    await cleanup_qr_message(context.bot, session)
    await cleanup_session_client(session)


def _new_session(chat_id: int, message_id: int, **extra) -> dict:
    base = {
        "chat_id": chat_id,
        "control_msg_id": message_id,
        "created_at": time.monotonic(),
    }
    base.update(extra)
    return base


# ============================================================================
# License helpers (UI)
# ============================================================================

def _license_status_label(rec: LicenseRecord) -> str:
    return {
        LICENSE_STATUS_ACTIVE: "🟢 Active",
        LICENSE_STATUS_LIFETIME: "⚫ Lifetime ♾️",
        LICENSE_STATUS_EXPIRED: "🟡 Expired",
        LICENSE_STATUS_REVOKED: "🔴 Revoked",
    }.get(rec.effective_status(), "❔")


def _license_expires_text(rec: LicenseRecord) -> str:
    if rec.is_lifetime():
        return "♾️ Lifetime"
    if not rec.expires_at:
        return "-"
    try:
        return datetime.fromisoformat(rec.expires_at).strftime("%Y-%m-%d %H:%M")
    except ValueError:
        return rec.expires_at


def _license_remaining_text(rec: LicenseRecord) -> str:
    if rec.is_lifetime():
        return "♾️"
    if rec.is_expired():
        return "❌ expired"
    try:
        secs = (datetime.fromisoformat(rec.expires_at) - _utcnow()).total_seconds()
        d, h = int(secs // 86400), int((secs % 86400) // 3600)
        if d == 0 and h == 0:
            return "< 1 hour"
        if d == 0:
            return f"{h} hours"
        return f"{d} days {h} hours"
    except (TypeError, ValueError):
        return "?"


def _license_days_left_text(rec: LicenseRecord) -> str:
    if rec.is_lifetime():
        return "∞"
    if rec.is_expired():
        return "expired"
    try:
        secs = (datetime.fromisoformat(rec.expires_at) - _utcnow()).total_seconds()
        return f"{math.ceil(secs / 86400)}d"
    except (TypeError, ValueError):
        return "?"


async def _notify_license_event(bot_app, config: Config, user_id: Optional[int], text: str):
    if not user_id or not bot_app:
        return
    with suppress(Exception):
        await bot_app.bot.send_message(user_id, text, parse_mode=ParseMode.HTML)


def _redeem_cancel_kb():
    return [[InlineKeyboardButton("❌ Cancel", callback_data="lic_cancel_redeem")]]


async def _unauthorized_screen_content(user_id: int):
    lic = await get_user_license(user_id)
    if lic:
        text = (
            f"⌛ <b>Access inactive</b>\n\n{_license_status_label(lic)}\n"
            f"Key: <code>{html.escape(lic.key_preview)}</code>\n\n"
            f"Contact admin for renewal or reset."
        )
        kb = [[InlineKeyboardButton("🔑 My License", callback_data="lic_my")]]
    else:
        text = (
            "🔑 <b>Access Denied</b>\n\n"
            "You don't have a license yet.\n"
            "Send your license key to this chat, or press the button below."
        )
        kb = [[InlineKeyboardButton("🎫 Redeem License", callback_data="lic_redeem")], [InlineKeyboardButton("👨‍💻 Buy License", url="https://t.me/nifzz")]]
    return text, kb


# ============================================================================
# Redeem rate limit
# ============================================================================

def _check_redeem_rate_limit(user_id: int) -> Optional[str]:
    now = time.monotonic()
    attempts = [t for t in _redeem_attempts.get(user_id, []) if now - t < REDEEM_WINDOW_SECONDS]
    _redeem_attempts[user_id] = attempts
    if len(attempts) >= REDEEM_MAX_ATTEMPTS:
        wait = int(REDEEM_WINDOW_SECONDS - (now - attempts[0]) + 1)
        return f"⏳ Too many attempts. Try again in {wait // 60}m {wait % 60}s."
    return None


def _bump_redeem_fail(user_id: int):
    now = time.monotonic()
    attempts = _redeem_attempts.setdefault(user_id, [])
    attempts.append(now)
    recent = [t for t in attempts if now - t < REDEEM_WINDOW_SECONDS]
    if len(recent) == REDEEM_ALERT_THRESHOLD and _session_manager and _session_manager.bot_app:
        _session_manager.track(asyncio.create_task(_broadcast_to_admins(
            _session_manager.bot_app, _config,
            f"⚠️ <b>Redeem brute-force alert</b>\n"
            f"User: <code>{user_id}</code> — "
            f"{REDEEM_ALERT_THRESHOLD} failed attempts in 10 min.",
        )))


def _clear_redeem_fails(user_id: int):
    _redeem_attempts.pop(user_id, None)


# ============================================================================
# License views
# ============================================================================

async def license_manager_view(context, chat_id, message_id, page: int = 0):
    licenses = sorted((await _license_db.all()).values(), key=lambda r: r.created_at, reverse=True)
    if not licenses:
        await render(
            context, chat_id, message_id,
            "🛡️ <b>License Manager</b>\n\nNo licenses yet.",
            [[InlineKeyboardButton("➕ Generate New Key", callback_data="lic_gen")],
             [InlineKeyboardButton("🔙 Back", callback_data="menu")]],
        )
        return

    total_pages = max(1, (len(licenses) + ACCOUNTS_PER_PAGE - 1) // ACCOUNTS_PER_PAGE)
    page = max(0, min(page, total_pages - 1))
    chunk = licenses[page * ACCOUNTS_PER_PAGE: (page + 1) * ACCOUNTS_PER_PAGE]

    keyboard = []
    for rec in chunk:
        short = rec.key_hash[:12]
        icon = {
            LICENSE_STATUS_ACTIVE: "🟢", LICENSE_STATUS_LIFETIME: "⚫",
            LICENSE_STATUS_EXPIRED: "🟡", LICENSE_STATUS_REVOKED: "🔴",
        }.get(rec.effective_status(), "⚪")
        owner = f"id:{rec.owner_id}" if rec.owner_id else "-"
        keyboard.append([InlineKeyboardButton(
            f"{icon} {rec.key_preview} · {owner} · {_license_days_left_text(rec)}",
            callback_data=f"lic_detail_{short}",
        )])

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"lic_mgr_p_{page - 1}"))
    if page < total_pages - 1:
        nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"lic_mgr_p_{page + 1}"))
    if nav:
        keyboard.append(nav)
    keyboard.append([InlineKeyboardButton("➕ Generate New Key", callback_data="lic_gen")])
    keyboard.append([InlineKeyboardButton("🔙 Back", callback_data="menu")])

    await render(
        context, chat_id, message_id,
        f"🛡️ <b>License Manager</b> (page {page + 1}/{total_pages})",
        keyboard,
    )


async def license_detail_view(context, chat_id, message_id, short: str, banner: str = ""):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return

    status = rec.effective_status()
    owner_txt = f"<code>{rec.owner_id}</code>" if rec.owner_id else "<i>not redeemed yet</i>"
    quota_used = (await count_owned_accounts(rec.owner_id)) if rec.owner_id else 0

    text = (
        f"{banner}🛡️ <b>License Detail</b>\n\n"
        f"Key       : <code>{html.escape(rec.key_preview)}</code>\n"
        f"Hash      : <code>{rec.key_hash[:16]}...</code>\n"
        f"Status    : {_license_status_label(rec)}\n"
        f"Owner     : {owner_txt}\n"
        f"Created   : {rec.created_at[:16].replace('T', ' ')}\n"
        f"Redeemed  : {(rec.redeemed_at[:16].replace('T', ' ') if rec.redeemed_at else '-')}\n"
        f"Expires   : {_license_expires_text(rec)}\n"
        f"Quota     : {quota_used}/{rec.max_accounts} accounts\n"
    )
    if rec.note:
        text += f"Note      : {html.escape(rec.note)}\n"

    keyboard = []
    if status in (LICENSE_STATUS_ACTIVE, LICENSE_STATUS_EXPIRED):
        keyboard.append([
            InlineKeyboardButton("➕ 7d", callback_data=f"lic_ext_{short}_7"),
            InlineKeyboardButton("➕ 14d", callback_data=f"lic_ext_{short}_14"),
            InlineKeyboardButton("➕ 30d", callback_data=f"lic_ext_{short}_30"),
        ])
        keyboard.append([
            InlineKeyboardButton("➕ 60d", callback_data=f"lic_ext_{short}_60"),
            InlineKeyboardButton("➕ 90d", callback_data=f"lic_ext_{short}_90"),
            InlineKeyboardButton("➕ 180d", callback_data=f"lic_ext_{short}_180"),
        ])
        keyboard.append([
            InlineKeyboardButton("➕ 365d", callback_data=f"lic_ext_{short}_365"),
            InlineKeyboardButton("✏️ Custom", callback_data=f"lic_extc_{short}"),
        ])
        keyboard.append([
            InlineKeyboardButton("👥 Edit Quota", callback_data=f"lic_quota_{short}"),
        ])

    if status == LICENSE_STATUS_REVOKED:
        keyboard.append([InlineKeyboardButton("🟢 Unrevoke", callback_data=f"lic_unrev_{short}")])
    elif status in (LICENSE_STATUS_ACTIVE, LICENSE_STATUS_LIFETIME, LICENSE_STATUS_EXPIRED):
        keyboard.append([InlineKeyboardButton("🔴 Revoke", callback_data=f"lic_revoke_{short}")])

    if status in (LICENSE_STATUS_REVOKED, LICENSE_STATUS_EXPIRED):
        keyboard.append([InlineKeyboardButton("🗑 Delete Permanently", callback_data=f"lic_del_{short}")])

    keyboard.append([InlineKeyboardButton("🔙 Back", callback_data="lic_mgr")])
    await render(context, chat_id, message_id, text, keyboard)


async def my_license_view(context, chat_id, message_id, user_id: int):
    rec = await get_user_license(user_id)
    authorized = await is_authorized(user_id)

    if not rec:
        if authorized:
            kb = [[InlineKeyboardButton("🔙 Back", callback_data="menu")]]
        else:
            kb = [[InlineKeyboardButton("🎫 Redeem License", callback_data="lic_redeem")], [InlineKeyboardButton("👨‍💻 Buy License", url="https://t.me/nifzz")]]
        await render(
            context, chat_id, message_id,
            "🔑 <b>My License</b>\n\nYou don't have a license yet.",
            kb,
        )
        return

    used = await count_owned_accounts(user_id)
    text = (
        f"🔑 <b>My License</b>\n\n"
        f"Key        : <code>{html.escape(rec.key_preview)}</code>\n"
        f"Status     : {_license_status_label(rec)}\n"
        f"Time left  : {_license_remaining_text(rec)}\n"
        f"Account quota : {used}/{rec.max_accounts} used\n"
        f"Active since: {(rec.redeemed_at[:16].replace('T', ' ') if rec.redeemed_at else '-')}\n"
        f"Expires    : {_license_expires_text(rec)}\n"
    )

    if authorized:
        kb = [
            [InlineKeyboardButton("🔄 Refresh", callback_data="lic_my")],
            [InlineKeyboardButton("🔙 Back", callback_data="menu")],
        ]
    else:
        kb = [
            [InlineKeyboardButton("🔄 Refresh", callback_data="lic_my")],
            [InlineKeyboardButton("🔙 Back", callback_data="lic_back_unauth")],
        ]
    await render(context, chat_id, message_id, text, kb)


# ============================================================================
# License actions
# ============================================================================

async def license_generate_start(context, chat_id, message_id):
    await render(
        context, chat_id, message_id,
        "➕ <b>Generate License</b>\n\nChoose duration:", [
            [InlineKeyboardButton("7 days", callback_data="lic_gen_d7"),
             InlineKeyboardButton("14 days", callback_data="lic_gen_d14")],
            [InlineKeyboardButton("30 days", callback_data="lic_gen_d30"),
             InlineKeyboardButton("60 days", callback_data="lic_gen_d60")],
            [InlineKeyboardButton("90 days", callback_data="lic_gen_d90"),
             InlineKeyboardButton("180 days", callback_data="lic_gen_d180")],
            [InlineKeyboardButton("365 days", callback_data="lic_gen_d365"),
             InlineKeyboardButton("Lifetime ♾️", callback_data="lic_gen_dlife")],
            [InlineKeyboardButton("✏️ Custom Days", callback_data="lic_gen_dcustom")],
            [InlineKeyboardButton("🔙 Cancel", callback_data="lic_mgr")],
        ],
    )


async def license_generate_quota(context, chat_id, message_id, user_id, duration):
    _pending_lic_gen[user_id] = {"duration": duration}
    label = {
        "7": "7 days", "14": "14 days", "30": "30 days", "60": "60 days",
        "90": "90 days", "180": "180 days", "365": "365 days",
        "life": "Lifetime ♾️",
    }.get(duration, f"{duration} days")
    await render(
        context, chat_id, message_id,
        f"➕ <b>Generate License</b>\n\nDuration: {label}\nChoose account quota:", [
            [InlineKeyboardButton("1 account", callback_data="lic_gen_q1")],
            [InlineKeyboardButton("3 accounts", callback_data="lic_gen_q3")],
            [InlineKeyboardButton("5 accounts", callback_data="lic_gen_q5")],
            [InlineKeyboardButton("✏️ Custom Quota", callback_data="lic_gen_qcustom")],
            [InlineKeyboardButton("🔙 Cancel", callback_data="lic_mgr")],
        ],
    )


async def license_generate_execute(context, chat_id, message_id, user_id, duration, quota):
    plaintext = generate_key()
    key_hash = hash_key(plaintext, _config.license_salt)
    preview = mask_key(plaintext)
    expires_at = None if duration == "life" else (
        _utcnow() + timedelta(days=int(duration))
    ).isoformat()
    rec = LicenseRecord(
        key_hash=key_hash,
        key_preview=preview,
        status=LICENSE_STATUS_ACTIVE,
        max_accounts=quota,
        expires_at=expires_at,
        created_by=user_id,
    )
    await _license_db.add(rec)
    audit_logger.info(
        "license_generated key=%s quota=%d duration=%s by=%d",
        preview, quota, duration, user_id,
    )
    dur_label = "Lifetime ♾️" if duration == "life" else f"{duration} days"
    text = (
        f"✅ <b>License Created</b>\n\n"
        f"Key        : <code>{html.escape(plaintext)}</code>\n"
        f"Duration   : {dur_label}\n"
        f"Account quota : {quota}\n\n"
        f"⚠️ <b>Save this key now.</b> Plaintext will not be shown again."
    )
    await render(
        context, chat_id, message_id, text,
        [[InlineKeyboardButton("🛡️ License Manager", callback_data="lic_mgr")]],
    )


async def license_extend_execute(context, chat_id, message_id, short, days):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    status = rec.effective_status()
    if status == LICENSE_STATUS_LIFETIME:
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Lifetime cannot be extended.\n\n")
        return
    if status == LICENSE_STATUS_REVOKED:
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Revoked. Unrevoke first.\n\n")
        return
    now = _utcnow()
    base = now if rec.is_expired(now) else datetime.fromisoformat(rec.expires_at)
    rec.expires_at = (base + timedelta(days=days)).isoformat()
    rec.expiry_notified_at = None
    rec.touch()
    await _license_db.update(rec)
    audit_logger.info(
        "license_extended key=%s days=%d new_exp=%s",
        rec.key_preview, days, rec.expires_at,
    )
    if rec.owner_id:
        await _notify_license_event(
            _session_manager.bot_app, _config, rec.owner_id,
            f"✅ <b>License Extended</b>\n\n"
            f"Key: <code>{html.escape(rec.key_preview)}</code>\n"
            f"Added: {days} days\n"
            f"Expires: {_license_expires_text(rec)}",
        )
    await license_detail_view(context, chat_id, message_id, short,
                              banner=f"✅ Extend +{days}d successful.\n\n")


async def license_edit_quota_execute(context, chat_id, message_id, short, new_quota):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return

    old_quota = rec.max_accounts
    rec.max_accounts = new_quota
    rec.touch()
    await _license_db.update(rec)
    
    audit_logger.info(
        "license_quota_edited key=%s old=%d new=%d",
        rec.key_preview, old_quota, new_quota,
    )
    
    if rec.owner_id:
        await _notify_license_event(
            _session_manager.bot_app, _config, rec.owner_id,
            f"👥 <b>License Quota Updated</b>\n\n"
            f"Key: <code>{html.escape(rec.key_preview)}</code>\n"
            f"Quota: {old_quota} → <b>{new_quota}</b> accounts",
        )
        
    await license_detail_view(
        context, chat_id, message_id, short,
        banner=f"✅ Quota updated: {old_quota} → {new_quota}.\n\n",
    )


async def license_revoke_confirm(context, chat_id, message_id, short):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    await render(
        context, chat_id, message_id,
        f"⚠️ Revoke <code>{html.escape(rec.key_preview)}</code>?\n\n"
        f"User will lose access. Accounts remain but cannot be accessed.", [
            [InlineKeyboardButton("✅ Yes, Revoke", callback_data=f"lic_revokeyes_{short}"),
             InlineKeyboardButton("❌ Cancel", callback_data=f"lic_detail_{short}")],
        ],
    )


async def license_revoke_execute(context, chat_id, message_id, short, admin_id):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    if rec.status == LICENSE_STATUS_REVOKED:
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Already revoked.\n\n")
        return
    rec.status = LICENSE_STATUS_REVOKED
    rec.revoked_at = _utcnow().isoformat()
    rec.revoked_by = admin_id
    rec.touch()
    await _license_db.update(rec)
    audit_logger.info("license_revoked key=%s by=%d", rec.key_preview, admin_id)
    if rec.owner_id:
        await _notify_license_event(
            _session_manager.bot_app, _config, rec.owner_id,
            f"🚫 <b>License Revoked</b>\n\n"
            f"Key: <code>{html.escape(rec.key_preview)}</code>\n\n"
            f"Your access to the bot has been terminated. Contact admin.",
        )
    await license_detail_view(context, chat_id, message_id, short,
                              banner="✅ Revoked.\n\n")


async def license_unrevoke_execute(context, chat_id, message_id, short):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    if rec.status != LICENSE_STATUS_REVOKED:
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Not revoked.\n\n")
        return
    rec.status = LICENSE_STATUS_ACTIVE
    rec.revoked_at = None
    rec.revoked_by = None
    rec.touch()
    await _license_db.update(rec)
    audit_logger.info("license_unrevoked key=%s", rec.key_preview)
    if rec.owner_id:
        await _notify_license_event(
            _session_manager.bot_app, _config, rec.owner_id,
            f"✅ <b>License Restored</b>\n\n"
            f"Key: <code>{html.escape(rec.key_preview)}</code>\n"
            f"Expires: {_license_expires_text(rec)}",
        )
    await license_detail_view(context, chat_id, message_id, short,
                              banner="✅ Unrevoked.\n\n")


async def license_delete_confirm(context, chat_id, message_id, short):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    if rec.effective_status() not in (LICENSE_STATUS_REVOKED, LICENSE_STATUS_EXPIRED):
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Only revoked/expired can be deleted.\n\n")
        return
    await render(
        context, chat_id, message_id,
        f"⚠️ <b>Permanently delete</b> <code>{html.escape(rec.key_preview)}</code>?\n\n"
        f"Cannot be undone. Owner's accounts remain.", [
            [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"lic_delyes_{short}"),
             InlineKeyboardButton("❌ Cancel", callback_data=f"lic_detail_{short}")],
        ],
    )


async def license_delete_execute(context, chat_id, message_id, short):
    rec = await _license_db.find_by_short_hash(short)
    if not rec:
        await license_manager_view(context, chat_id, message_id)
        return
    if rec.effective_status() not in (LICENSE_STATUS_REVOKED, LICENSE_STATUS_EXPIRED):
        await license_detail_view(context, chat_id, message_id, short,
                                  banner="⚠️ Cannot be deleted.\n\n")
        return
    await _license_db.delete(rec.key_hash)
    audit_logger.info("license_deleted key=%s", rec.key_preview)
    await license_manager_view(context, chat_id, message_id)


# ============================================================================
# Redeem (text-based, no slash command)
# ============================================================================

async def _do_redeem(context, user_id: int, chat_id: int, normalized: str):
    session = user_sessions.get(user_id)
    message_id = session.get("control_msg_id") if session else None

    async def reply(text, kb=None):
        nonlocal message_id
        if message_id:
            new_id = await render(context, chat_id, message_id, text, kb)
            if new_id != message_id:
                message_id = new_id
                if user_id in user_sessions:
                    user_sessions[user_id]["control_msg_id"] = new_id
        else:
            msg = await context.bot.send_message(
                chat_id, text, parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup(kb) if kb else None,
            )
            user_sessions[user_id] = _new_session(msg.chat_id, msg.message_id)
            message_id = msg.message_id

    if _license_db is None:
        await reply("❌ License system not initialized.")
        return

    limit_msg = _check_redeem_rate_limit(user_id)
    if limit_msg:
        await reply(limit_msg, _redeem_cancel_kb())
        return

    if await get_user_license(user_id):
        await reply("⚠️ You already have a license. Contact admin for reset.",
                    _redeem_cancel_kb())
        return

    rec = await _license_db.find_by_plaintext(normalized)
    if rec is None:
        _bump_redeem_fail(user_id)
        await reply("❌ Key not found.", _redeem_cancel_kb())
        return
    if rec.owner_id is not None:
        _bump_redeem_fail(user_id)
        await reply("❌ Key already redeemed by another user.", _redeem_cancel_kb())
        return
    if not rec.is_usable():
        _bump_redeem_fail(user_id)
        st = {"revoked": "revoked", "expired": "expired"}.get(
            rec.effective_status(), "invalid")
        await reply(f"❌ Key {st}.", _redeem_cancel_kb())
        return

    rec.owner_id = user_id
    rec.redeemed_at = _utcnow().isoformat()
    rec.touch()
    await _license_db.update(rec)
    _clear_redeem_fails(user_id)
    audit_logger.info("license_redeemed key=%s owner=%d", rec.key_preview, user_id)

    await reply(
        f"🎉 <b>License Active</b>\n\n"
        f"Key: <code>{html.escape(rec.key_preview)}</code>\n"
        f"Status: {_license_status_label(rec)}\n"
        f"Expires: {_license_expires_text(rec)}\n"
        f"Account quota: {rec.max_accounts}\n\n"
        f"Press the button below to start.",
        [[InlineKeyboardButton("🏠 Menu", callback_data="menu")]],
    )
    await _broadcast_to_admins(
        _session_manager.bot_app if _session_manager else None, _config,
        f"🔑 License redeemed: <code>{html.escape(rec.key_preview)}</code> "
        f"by <code>{user_id}</code>",
    )


async def _handle_unauthorized_text(update, context, user_id: int, text: str):
    chat_id = update.effective_chat.id
    with suppress(Exception):
        await context.bot.delete_message(chat_id, update.message.message_id)

    normalized = normalize_key(text) if text else None
    if normalized:
        await _do_redeem(context, user_id, chat_id, normalized)
        return

    session = user_sessions.get(user_id)
    message_id = session.get("control_msg_id") if session else None
    text_content, kb = await _unauthorized_screen_content(user_id)

    if message_id:
        await render(context, chat_id, message_id, text_content, kb)
    else:
        msg = await context.bot.send_message(
            chat_id, text_content, parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup(kb),
        )
        user_sessions[user_id] = _new_session(msg.chat_id, msg.message_id)


# ============================================================================
# Commands
# ============================================================================

async def start_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user is None or update.message is None:
        return
    user_id = update.effective_user.id

    if not await is_authorized(user_id):
        await reset_user_flow(context, user_id)
        text_content, kb = await _unauthorized_screen_content(user_id)
        msg = await update.message.reply_text(
            text_content,
            parse_mode=ParseMode.HTML,
            reply_markup=InlineKeyboardMarkup(kb),
        )
        user_sessions[user_id] = _new_session(msg.chat_id, msg.message_id)
        return

    await reset_user_flow(context, user_id)
    message = await update.message.reply_text(
        "🛡️ <b>Welcome to Anti-Login Bot</b>\n"
        "Securely manage and monitor your protected accounts.\n\n"
        "👨‍💻 Developer: @nifzz",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(main_menu_keyboard(user_id)),
    )
    user_sessions[user_id] = _new_session(message.chat_id, message.message_id)


async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user is None or update.message is None:
        return
    user_id = update.effective_user.id
    if not await is_authorized(user_id):
        await _handle_unauthorized_text(update, context, user_id, "")
        return
    await reset_user_flow(context, user_id)
    msg = await update.message.reply_text(
        "✅ Canceled.",
        reply_markup=InlineKeyboardMarkup(main_menu_keyboard(user_id)),
    )
    user_sessions[user_id] = _new_session(msg.chat_id, msg.message_id)


# ============================================================================
# QR
# ============================================================================

def generate_qr_image(url: str) -> io.BytesIO:
    img = qrcode.make(url)
    buf = io.BytesIO()
    img.save(buf, "PNG")
    buf.seek(0)
    return buf


async def _refresh_qr_token(client, qr_login):
    resp = await client(functions.auth.ExportLoginTokenRequest(
        _config.api_id, _config.api_hash, []
    ))
    if isinstance(resp, types.auth.LoginTokenMigrateTo):
        if not hasattr(client, "_switch_dc"):
            logger.error("Telethon private _switch_dc missing — cannot migrate DC")
            raise RuntimeError("Telethon API changed: _switch_dc not available")
        await client._switch_dc(resp.dc_id)
        resp = await client(functions.auth.ImportLoginTokenRequest(resp.token))
    qr_login._resp = resp
    return resp


async def refresh_qr_photo(context, session: dict, qr_login) -> bool:
    try:
        buf = generate_qr_image(qr_login.url)
    except Exception as e:
        logger.error("Failed to regenerate QR image: %s", e)
        return False
    try:
        await context.bot.edit_message_media(
            chat_id=session["chat_id"],
            message_id=session["qr_msg_id"],
            media=InputMediaPhoto(
                buf,
                caption=(
                    "🔲 Scan this QR code from Telegram on your phone:\n"
                    "Settings → Devices → Link Desktop Device\n\n"
                    "♻️ Code refreshed — please scan the latest one."
                ),
            ),
        )
        return True
    except Exception as e:
        logger.error("Failed to refresh QR image: %s", e)
        return False


async def start_qr_login(context, chat_id, message_id, user_id):
    client = TelegramClient(StringSession(), _config.api_id, _config.api_hash)
    try:
        await client.connect()
        qr_login = await client.qr_login()
    except Exception as e:
        logger.error("QR login setup failed: %s", e)
        with suppress(Exception):
            await client.disconnect()
        await render(context, chat_id, message_id,
                     f"❌ QR login failed: {html.escape(str(e))}", add_method_keyboard())
        return

    try:
        buf = generate_qr_image(qr_login.url)
    except Exception as e:
        logger.error("Failed to generate QR image: %s", e)
        with suppress(Exception):
            await client.disconnect()
        await render(
            context, chat_id, message_id,
            "❌ QR code generation failed (missing Pillow?). Install it with:\n"
            "<code>pip install \"qrcode[pil]\"</code>\n\n"
            "Or use the Phone Number method instead.",
            add_method_keyboard(),
        )
        return

    try:
        sent = await context.bot.send_photo(
            chat_id, buf,
            caption=(
                "🔲 Scan this QR code from Telegram on your phone:\n"
                "Settings → Devices → Link Desktop Device"
            ),
        )
    except Exception as e:
        logger.error("Failed to send QR photo: %s", e)
        with suppress(Exception):
            await client.disconnect()
        await render(context, chat_id, message_id,
                     f"❌ Failed to send QR image: {html.escape(str(e))}",
                     add_method_keyboard())
        return

    user_sessions[user_id] = _new_session(
        chat_id, message_id,
        step="wait_qr",
        client=client,
        qr_login=qr_login,
        qr_msg_id=sent.message_id,
    )
    await render(context, chat_id, message_id, "⏳ Waiting for QR scan...", cancel_keyboard())
    _session_manager.track(asyncio.create_task(watch_qr_login(context, user_id)))


async def watch_qr_login(context, user_id):
    session = user_sessions.get(user_id)
    if not session or session.get("step") != "wait_qr":
        return
    client = session["client"]
    chat_id = session["chat_id"]
    message_id = session["control_msg_id"]

    for attempt in range(QR_MAX_REFRESHES):
        if user_sessions.get(user_id) is not session:
            return
        qr_login = session["qr_login"]
        try:
            await qr_login.wait()
            break
        except SessionPasswordNeededError:
            if user_sessions.get(user_id) is session:
                session["step"] = "wait_password"
                await render(context, chat_id, message_id,
                             "🔐 This account has 2FA enabled. Enter the password:",
                             cancel_keyboard())
            return
        except asyncio.TimeoutError:
            if user_sessions.get(user_id) is not session:
                return
            if attempt == QR_MAX_REFRESHES - 1:
                await cleanup_qr_message(context.bot, session)
                user_sessions.pop(user_id, None)
                await render(
                    context, chat_id, message_id,
                    "⌛ QR code expired.",
                    [[InlineKeyboardButton("🔄 Retry", callback_data="add_qr"),
                      InlineKeyboardButton("🔙 Menu", callback_data="menu")]],
                )
                with suppress(Exception):
                    await client.disconnect()
                return
            try:
                await _refresh_qr_token(client, qr_login)
            except SessionPasswordNeededError:
                if user_sessions.get(user_id) is session:
                    session["step"] = "wait_password"
                    await cleanup_qr_message(context.bot, session)
                    await render(context, chat_id, message_id,
                                 "🔐 This account has 2FA enabled. Enter the password:",
                                 cancel_keyboard())
                return
            except Exception as e:
                logger.error("Failed to recreate QR token: %s", e)
                await cleanup_qr_message(context.bot, session)
                user_sessions.pop(user_id, None)
                await render(context, chat_id, message_id,
                             f"❌ QR login failed: {html.escape(str(e))}",
                             [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]])
                with suppress(Exception):
                    await client.disconnect()
                return
            await refresh_qr_photo(context, session, qr_login)
            continue
        except Exception as e:
            logger.error("QR login failed: %s", e)
            if user_sessions.get(user_id) is session:
                await cleanup_qr_message(context.bot, session)
                user_sessions.pop(user_id, None)
                await render(context, chat_id, message_id,
                             f"❌ QR login failed: {html.escape(str(e))}",
                             [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]])
            with suppress(Exception):
                await client.disconnect()
            return

    try:
        me = await client.get_me()
    except Exception as e:
        logger.error("QR login: get_me failed: %s", e)
        await cleanup_qr_message(context.bot, session)
        user_sessions.pop(user_id, None)
        with suppress(Exception):
            await client.disconnect()
        await render(context, chat_id, message_id,
                     f"❌ Could not fetch account info: {html.escape(str(e))}",
                     [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]])
        return

    if me is None:
        logger.error("QR login: get_me returned None")
        await cleanup_qr_message(context.bot, session)
        user_sessions.pop(user_id, None)
        with suppress(Exception):
            await client.disconnect()
        await render(context, chat_id, message_id,
                     "❌ Could not fetch account info.",
                     [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]])
        return

    if user_sessions.get(user_id) is not session:
        with suppress(Exception):
            await client.disconnect()
        return

    phone = normalize_phone(me.phone) if me.phone else f"+id{me.id}"
    await cleanup_qr_message(context.bot, session)
    _add_cooldown[user_id] = time.monotonic()
    await finish_add_account(context, chat_id, message_id, user_id, phone, client)


# ============================================================================
# Sweepers
# ============================================================================

async def user_session_sweeper(bot):
    while True:
        await asyncio.sleep(USER_SESSION_SWEEP_INTERVAL)
        now = time.monotonic()
        stale = []
        for uid, sess in list(user_sessions.items()):
            created = sess.get("created_at", now)
            has_step = "step" in sess
            timeout = STEP_TIMEOUT_SECONDS if has_step else USER_SESSION_IDLE_TIMEOUT
            if now - created > timeout:
                stale.append(uid)

        for uid in stale:
            sess = user_sessions.pop(uid, None)
            if sess:
                await cleanup_qr_message(bot, sess)
                await cleanup_session_client(sess)
        if stale:
            logger.info("Swept %d idle user session(s)", len(stale))

        # Cleanup pending license gen state
        for uid in list(_pending_lic_gen.keys()):
            sess = user_sessions.get(uid)
            if not sess or (now - sess.get("created_at", now)) > USER_SESSION_IDLE_TIMEOUT:
                _pending_lic_gen.pop(uid, None)

        # Cleanup stale redeem attempts
        for uid in list(_redeem_attempts.keys()):
            recent = [t for t in _redeem_attempts[uid] if now - t < REDEEM_WINDOW_SECONDS]
            if recent:
                _redeem_attempts[uid] = recent
            else:
                _redeem_attempts.pop(uid, None)

        if _session_manager:
            cutoff = time.monotonic() - UI_CACHE_TTL_SECONDS
            _session_manager._ui_sessions = {
                k: v for k, v in _session_manager._ui_sessions.items()
                if len(v) >= 3 and v[2] > cutoff
            }


# ============================================================================
# Message handler
# ============================================================================

async def message_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_user is None or update.message is None:
        return
    user_id = update.effective_user.id
    session = user_sessions.get(user_id)
    text = (update.message.text or "").strip()

    if not await is_authorized(user_id):
        await _handle_unauthorized_text(update, context, user_id, text)
        return

    if not session or "step" not in session:
        with suppress(Exception):
            await context.bot.delete_message(update.effective_chat.id, update.message.message_id)
        return

    chat_id = session["chat_id"]
    message_id = session["control_msg_id"]

    with suppress(Exception):
        await context.bot.delete_message(chat_id, update.message.message_id)

    if not text:
        await render(context, chat_id, message_id,
                     "❌ Empty input is not allowed. Please try again.",
                     cancel_keyboard())
        return

    step = session["step"]

    if step == "wait_phone":
        if not PHONE_REGEX.match(text) or text.startswith("+id"):
            await render(
                context, chat_id, message_id,
                "❌ Invalid format. Use <code>+&lt;country code&gt;&lt;number&gt;</code>, digits only.",
                cancel_keyboard(),
            )
            return
        if await _session_manager.database.contains(text):
            await render(
                context, chat_id, message_id,
                f"⚠️ Account <code>{html.escape(text)}</code> already registered.",
                cancel_keyboard(),
            )
            return
        client = TelegramClient(StringSession(), _config.api_id, _config.api_hash)
        try:
            await client.connect()
            await client.send_code_request(text)
        except PhoneNumberInvalidError:
            with suppress(Exception):
                await client.disconnect()
            await render(context, chat_id, message_id, "❌ Invalid phone number.",
                         cancel_keyboard())
            return
        except FloodWaitError as e:
            with suppress(Exception):
                await client.disconnect()
            await render(context, chat_id, message_id,
                         f"⏳ Please wait {e.seconds} seconds and try again.",
                         cancel_keyboard())
            return
        except Exception as e:
            with suppress(Exception):
                await client.disconnect()
            await render(context, chat_id, message_id,
                         f"❌ Error: {html.escape(str(e))}", cancel_keyboard())
            return
        session.update({"step": "wait_code", "phone": text, "client": client})
        _add_cooldown[user_id] = time.monotonic()
        await render(
            context, chat_id, message_id,
            f"📲 Code sent to <code>{html.escape(text)}</code>.\n"
            f"Enter the code (e.g. <code>12345</code> or <code>1 2 3 4 5</code>):",
            cancel_keyboard(),
        )

    elif step == "wait_code":
        code = re.sub(r"\D", "", text)
        if not CODE_REGEX.match(code):
            await render(
                context, chat_id, message_id,
                "❌ The code must be numeric only. Try again\n"
                "(<code>12345</code> or <code>1 2 3 4 5</code>):",
                cancel_keyboard(),
            )
            return
        phone, client = session["phone"], session["client"]
        try:
            await client.sign_in(phone, code)
            await finish_add_account(context, chat_id, message_id, user_id, phone, client)
        except SessionPasswordNeededError:
            session["step"] = "wait_password"
            await render(context, chat_id, message_id,
                         "🔐 This account has 2FA enabled. Enter the password:",
                         cancel_keyboard())
        except PhoneCodeInvalidError:
            await render(context, chat_id, message_id, "❌ Invalid code, try again:",
                         cancel_keyboard())
        except PhoneCodeExpiredError:
            await cleanup_session_client(session)
            user_sessions.pop(user_id, None)
            await render(context, chat_id, message_id, "❌ Code expired. Please start over.",
                         [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]])
        except FloodWaitError as e:
            await render(context, chat_id, message_id,
                         f"⏳ Please wait {e.seconds} seconds and try again.",
                         cancel_keyboard())
        except Exception as e:
            await render(context, chat_id, message_id,
                         f"❌ Error: {html.escape(str(e))}", cancel_keyboard())

    elif step == "wait_custom_days":
        if not is_super_admin(user_id):
            return
        try:
            days = int(text)
        except ValueError:
            await render(context, chat_id, message_id,
                         "❌ Send a whole number (1-3650).",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        if not (1 <= days <= 3650):
            await render(context, chat_id, message_id,
                         "❌ Range: 1-3650 days.",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        user_sessions.pop(user_id, None)
        await license_generate_quota(context, chat_id, message_id, user_id, str(days))

    elif step == "wait_custom_quota":
        if not is_super_admin(user_id):
            return
        try:
            quota = int(text)
        except ValueError:
            await render(context, chat_id, message_id,
                         "❌ Send a whole number (1-100).",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        if not (1 <= quota <= 100):
            await render(context, chat_id, message_id,
                         "❌ Range: 1-100 accounts.",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        
        pending = _pending_lic_gen.pop(user_id, {})
        duration = pending.get("duration", "30")
        user_sessions.pop(user_id, None)
        
        await license_generate_execute(context, chat_id, message_id, user_id, duration, quota)

    elif step == "wait_extend_days":
        if not is_super_admin(user_id):
            return
        try:
            days = int(text)
        except ValueError:
            await render(context, chat_id, message_id,
                         "❌ Send a whole number (1-3650).",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        if not (1 <= days <= 3650):
            await render(context, chat_id, message_id,
                         "❌ Range: 1-3650 days.",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        short = session.get("lic_short")
        user_sessions.pop(user_id, None)
        if short:
            await license_extend_execute(context, chat_id, message_id, short, days)

    elif step == "wait_quota_value":
        if not is_super_admin(user_id):
            return
        try:
            quota = int(text)
        except ValueError:
            await render(context, chat_id, message_id,
                         "❌ Send a whole number (1-100).",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        if not (1 <= quota <= 100):
            await render(context, chat_id, message_id,
                         "❌ Range: 1-100 accounts.",
                         [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]])
            return
        short = session.get("lic_short")
        user_sessions.pop(user_id, None)
        if short:
            await license_edit_quota_execute(context, chat_id, message_id, short, quota)

    elif step == "wait_password":
        client = session["client"]
        phone = session.get("phone")
        try:
            await client.sign_in(password=text)
            if not phone:
                me = await client.get_me()
                if me is None:
                    raise RuntimeError("get_me returned None")
                phone = normalize_phone(me.phone) if me.phone else f"+id{me.id}"
            await cleanup_qr_message(context.bot, session)
            await finish_add_account(context, chat_id, message_id, user_id, phone, client)
        except PasswordHashInvalidError:
            await render(context, chat_id, message_id,
                         "❌ Incorrect password. Please try again:",
                         cancel_keyboard())
        except Exception as e:
            logger.error("Password login failed for %s: %s", phone, e)
            await cleanup_qr_message(context.bot, session)
            user_sessions.pop(user_id, None)
            with suppress(Exception):
                await client.disconnect()
            await render(
                context, chat_id, message_id,
                f"❌ Login failed: {html.escape(str(e))}",
                [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]],
            )


async def finish_add_account(context, chat_id, message_id, user_id, phone, client):
    if not PHONE_REGEX.match(phone):
        logger.error("Refusing to add account with invalid identifier: %r", phone)
        with suppress(Exception):
            await client(functions.auth.LogOutRequest())
        with suppress(Exception):
            await client.disconnect()
        user_sessions.pop(user_id, None)
        await render(
            context, chat_id, message_id,
            f"❌ Invalid account identifier: <code>{html.escape(phone)}</code>",
            [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]],
        )
        return

    qerr = await _check_license_quota(user_id)
    if qerr:
        with suppress(Exception):
            await client(functions.auth.LogOutRequest())
        with suppress(Exception):
            await client.disconnect()
        user_sessions.pop(user_id, None)
        await render(
            context, chat_id, message_id,
            f"❌ {html.escape(qerr)}",
            [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]],
        )
        return

    try:
        success = await _session_manager.add_account(phone, client, owner_id=user_id)
    except Exception as e:
        logger.error("finish_add_account: add_account failed for %s: %s", phone, e)
        success = False

    user_sessions.pop(user_id, None)

    if success:
        await account_detail_view(context, chat_id, message_id, user_id, phone,
                                  banner="✅ Account added successfully!\n\n")
        return

    with suppress(Exception):
        await client(functions.auth.LogOutRequest())
    with suppress(Exception):
        await client.disconnect()
    await render(
        context, chat_id, message_id,
        "❌ Account already exists or failed to add.",
        [[InlineKeyboardButton("🔙 Menu", callback_data="menu")]],
    )


# ============================================================================
# Callback dispatcher
# ============================================================================

async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if update.effective_user is None:
        return
    if query is None:
        return
    if query.message is None or not hasattr(query.message, "chat_id"):
        await _safe_answer(query, "Message expired — send /start again")
        return

    user_id = update.effective_user.id
    chat_id = query.message.chat_id
    message_id = query.message.message_id
    data = query.data

    # ===== Pre-auth: unauthorized users =====
    if not await is_authorized(user_id):
        if data == "lic_redeem":
            await _safe_answer(query)
            await reset_user_flow(context, user_id)
            user_sessions[user_id] = _new_session(chat_id, message_id)
            await render(
                context, chat_id, message_id,
                "🎫 <b>Redeem License</b>\n\n"
                "Send your key as a text message.\n"
                "Format: <code>AL-XXXX-XXXX-XXXX-XXXX-YY</code>",
                _redeem_cancel_kb(),
            )
            return
        if data in ("lic_cancel_redeem", "lic_back_unauth"):
            await _safe_answer(query)
            await reset_user_flow(context, user_id)
            text_content, kb = await _unauthorized_screen_content(user_id)
            await render(context, chat_id, message_id, text_content, kb)
            user_sessions[user_id] = _new_session(chat_id, message_id)
            return
        if data == "lic_my":
            await _safe_answer(query)
            await my_license_view(context, chat_id, message_id, user_id)
            return
        await _safe_answer(query, "⛔ Unauthorized", show_alert=True)
        return

    # ===== Pre-ACK: cooldown + quota =====
    if data in ("add_acc", "add_phone", "add_qr"):
        cd = _check_add_cooldown(user_id)
        if cd:
            await _safe_answer(query, cd, show_alert=True)
            if data == "add_acc":
                await show_main_menu(context, chat_id, message_id, user_id)
            else:
                await render(context, chat_id, message_id,
                             "Choose an account addition method:", add_method_keyboard())
            return
        qerr = await _check_license_quota(user_id)
        if qerr:
            await _safe_answer(query, qerr, show_alert=True)
            if data == "add_acc":
                await show_main_menu(context, chat_id, message_id, user_id)
            else:
                await render(context, chat_id, message_id,
                             "Choose an account addition method:", add_method_keyboard())
            return

    # ===== Session op parsing =====
    _session_op = None
    if data.startswith("sess_trust_"):
        short = data[len("sess_trust_"):]
        entry = _session_manager._ui_sessions.pop(short, None)
        if not entry or len(entry) < 2:
            await _safe_answer(query, "Expired — reopen Sessions")
            return
        phone, hash_val = entry[0], entry[1]
        if not await can_manage_account(user_id, phone):
            await _safe_answer(query, "No access")
            return
        if not _session_manager.clients.get(phone):
            await _safe_answer(query, "Account unavailable")
            return
        _session_op = ("trust", phone, hash_val, None)
    elif data.startswith("sess_revoke_"):
        short = data[len("sess_revoke_"):]
        entry = _session_manager._ui_sessions.pop(short, None)
        if not entry or len(entry) < 2:
            await _safe_answer(query, "Expired — reopen Sessions")
            return
        phone, hash_val = entry[0], entry[1]
        if not await can_manage_account(user_id, phone):
            await _safe_answer(query, "No access")
            return
        if not _session_manager.clients.get(phone):
            await _safe_answer(query, "Account unavailable")
            return
        _session_op = ("revoke", phone, hash_val, None)
    elif data.startswith("revokeconfirm_"):
        short = data[len("revokeconfirm_"):]
        entry = _session_manager._ui_sessions.get(short)
        if not entry or len(entry) < 2:
            await _safe_answer(query, "Expired — reopen Sessions")
            return
        phone, hash_val = entry[0], entry[1]
        if not await can_manage_account(user_id, phone):
            await _safe_answer(query, "No access")
            return
        if not _session_manager.clients.get(phone):
            await _safe_answer(query, "Account unavailable")
            return
        _session_op = ("confirm", phone, hash_val, short)

    await _safe_answer(query)

    try:
        await reset_user_flow(context, user_id)
        user_sessions[user_id] = _new_session(chat_id, message_id)

        # ===== Session ops =====
        if _session_op is not None:
            kind, phone, hash_val, short = _session_op
            client = _session_manager.clients.get(phone)
            if not client:
                await list_accounts_view(context, chat_id, message_id, user_id)
                return
            try:
                result = await client(functions.account.GetAuthorizationsRequest())
            except Exception as e:
                logger.error("Failed to load sessions for %s (%s): %s", phone, kind, e)
                await sessions_view(context, chat_id, message_id, user_id, phone,
                                    banner=f"❌ Failed to load sessions: {html.escape(str(e))}\n\n")
                return

            if kind == "trust":
                matched = next((a for a in result.authorizations if a.hash == hash_val), None)
                if matched is None:
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="⚠️ Session not found (may already be gone).\n\n")
                    return

                def _trust(r):
                    _session_manager._whitelist_session(r, matched, source="admin_ui")

                await _session_manager.database.mutate(phone, _trust)
                audit_logger.info("session_trusted_manual phone=%s hash=%s", phone, matched.hash)
                await sessions_view(context, chat_id, message_id, user_id, phone,
                                    banner="✅ Session trusted.\n\n")

            elif kind == "revoke":
                matched = next((a for a in result.authorizations if a.hash == hash_val), None)
                if matched is None:
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="⚠️ Session not found (may already be gone).\n\n")
                    return
                if matched.current:
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="⚠️ Refusing to revoke the current session.\n\n")
                    return
                try:
                    await client(functions.account.ResetAuthorizationRequest(hash=matched.hash))

                    def _drop(r):
                        r.whitelisted_sessions = [
                            e for e in r.whitelisted_sessions if e.get("hash") != matched.hash
                        ]

                    await _session_manager.database.mutate(phone, _drop)
                    audit_logger.warning("session_revoked_manual phone=%s hash=%s",
                                         phone, matched.hash)
                    logger.warning("Manually revoked session for %s", phone)
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="✅ Session revoked.\n\n")
                except Exception as e:
                    logger.error("Failed to revoke session for %s: %s", phone, e)
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner=f"❌ Failed to revoke: {html.escape(str(e))}\n\n")

            elif kind == "confirm":
                target = next((a for a in result.authorizations if a.hash == hash_val), None)
                if target is None:
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="⚠️ Session not found.\n\n")
                    return
                if target.current:
                    await sessions_view(context, chat_id, message_id, user_id, phone,
                                        banner="⚠️ Refusing to logout the current session.\n\n")
                    return
                keyboard = [[
                    InlineKeyboardButton("✅ Yes, Logout",
                                         callback_data=f"sess_revoke_{short}"),
                    InlineKeyboardButton("❌ Cancel",
                                         callback_data=f"sessions_{phone}"),
                ]]
                await render(
                    context, chat_id, message_id,
                    f"⚠️ <b>Logout this session?</b>\n\n"
                    f"Account: <code>{html.escape(phone)}</code>\n\n"
                    f"{_format_session(target)}"
                    f"\nThis session will be <b>terminated immediately on Telegram's servers</b>.\n"
                    f"The device will need to log in again.\n\n"
                    f"<b>This action cannot be undone.</b>",
                    keyboard,
                )
            return

        # ===== Normal dispatch =====
        if data == "menu":
            await show_main_menu(context, chat_id, message_id, user_id)

        elif data == "stats":
            db = await _session_manager.database.all()
            if not is_super_admin(user_id):
                db = {p: r for p, r in db.items() if r.owner_id == user_id}
            total = len(db)
            protected = sum(1 for r in db.values() if r.anti_login)
            codes = sum(r.invalidated_codes for r in db.values())
            sessions_count = sum(len(r.whitelisted_sessions) for r in db.values())
            no_baseline = sum(1 for r in db.values() if not r.whitelist_initialized)
            connected = sum(1 for p in db if p in _session_manager.clients)
            lic = await get_user_license(user_id) if not is_super_admin(user_id) else None
            quota_line = ""
            if lic:
                used = await count_owned_accounts(user_id)
                quota_line = f"\nAccount quota       : {used}/{lic.max_accounts}"
            text = (
                "📊 <b>Stats</b>\n"
                f"Accounts         : <b>{total}</b>\n"
                f"Connected        : {connected}\n"
                f"Protected        : {protected}\n"
                f"Codes invalid    : {codes}\n"
                f"Whitelisted      : {sessions_count}\n"
                f"⚠️ No baseline  : {no_baseline}"
                f"{quota_line}"
            )
            await render(context, chat_id, message_id, text,
                         [[InlineKeyboardButton("🔙 Back", callback_data="menu")]])

        elif data == "add_acc":
            await render(context, chat_id, message_id,
                         "Choose an account addition method:", add_method_keyboard())

        elif data == "add_phone":
            user_sessions[user_id]["step"] = "wait_phone"
            await render(
                context, chat_id, message_id,
                "📱 Send the phone number with country code:\n<code>+15551234567</code>",
                cancel_keyboard(),
            )

        elif data == "add_qr":
            await start_qr_login(context, chat_id, message_id, user_id)

        elif data == "cancel_add":
            await show_main_menu(context, chat_id, message_id, user_id)

        elif data == "list_acc":
            await list_accounts_view(context, chat_id, message_id, user_id, page=0)

        elif data.startswith("list_acc_"):
            try:
                page = int(data[len("list_acc_"):])
            except ValueError:
                page = 0
            await list_accounts_view(context, chat_id, message_id, user_id, page=page)

        elif data.startswith("acc_"):
            await account_detail_view(context, chat_id, message_id, user_id,
                                      data[len("acc_"):])

        elif data.startswith("toggle_"):
            phone = data[len("toggle_"):]
            if not await can_manage_account(user_id, phone):
                return
            await _session_manager.toggle_anti_login(phone)
            await account_detail_view(context, chat_id, message_id, user_id, phone)

        elif data.startswith("resetbase_"):
            phone = data[len("resetbase_"):]
            if not await can_manage_account(user_id, phone):
                return
            ok = await _session_manager.reset_baseline(phone)
            banner = "✅ Baseline in-reset.\n\n" if ok else "❌ Reset baseline failed.\n\n"
            await account_detail_view(context, chat_id, message_id, user_id, phone, banner=banner)

        elif data.startswith("delconfirm_"):
            phone = data[len("delconfirm_"):]
            if not await can_manage_account(user_id, phone):
                return
            ok = await _session_manager.remove_account(phone)
            if ok:
                await render(
                    context, chat_id, message_id,
                    f"✅ Account <code>{html.escape(phone)}</code> removed and session logged out.",
                    [[InlineKeyboardButton("🔙 Back", callback_data="list_acc")]],
                )
            else:
                await render(
                    context, chat_id, message_id,
                    f"⚠️ Account <code>{html.escape(phone)}</code> could not be fully removed "
                    f"(logout may have failed). Try again or check the log.",
                    [[InlineKeyboardButton("🔙 Back", callback_data="list_acc")]],
                )

        elif data.startswith("del_"):
            await delete_confirm_view(context, chat_id, message_id, user_id,
                                      data[len("del_"):])

        elif data == "reconnect_all":
            if not is_super_admin(user_id):
                return
            await render(context, chat_id, message_id,
                         "🔄 Reconnecting all accounts in background...")
            _session_manager.track(asyncio.create_task(_session_manager.reconnect_all()))
            await show_main_menu(context, chat_id, message_id, user_id)

        elif data.startswith("sessions_"):
            phone = data[len("sessions_"):]
            if not await can_manage_account(user_id, phone):
                return
            await sessions_view(context, chat_id, message_id, user_id, phone)

        # ===== License dispatch =====
        elif data == "lic_my":
            await my_license_view(context, chat_id, message_id, user_id)

        elif data == "lic_mgr":
            if not is_super_admin(user_id):
                return
            await license_manager_view(context, chat_id, message_id, page=0)

        elif data.startswith("lic_mgr_p_"):
            if not is_super_admin(user_id):
                return
            try:
                page = int(data[len("lic_mgr_p_"):])
            except ValueError:
                page = 0
            await license_manager_view(context, chat_id, message_id, page=page)

        elif data == "lic_gen":
            if not is_super_admin(user_id):
                return
            await license_generate_start(context, chat_id, message_id)

        elif data == "lic_gen_dcustom":
            if not is_super_admin(user_id):
                return
            user_sessions[user_id]["step"] = "wait_custom_days"
            await render(
                context, chat_id, message_id,
                "✏️ Send the number of days for the license (1-3650):",
                [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]],
            )

        elif data.startswith("lic_gen_d"):
            if not is_super_admin(user_id):
                return
            await license_generate_quota(context, chat_id, message_id, user_id,
                                        data[len("lic_gen_d"):])

        elif data == "lic_gen_qcustom":
            if not is_super_admin(user_id):
                return
            user_sessions[user_id]["step"] = "wait_custom_quota"
            await render(
                context, chat_id, message_id,
                "✏️ Send the number of account quota (1-100):",
                [[InlineKeyboardButton("❌ Cancel", callback_data="lic_mgr")]],
            )

        elif data.startswith("lic_gen_q"):
            if not is_super_admin(user_id):
                return
            try:
                quota = int(data[len("lic_gen_q"):])
            except ValueError:
                return
            pending = _pending_lic_gen.pop(user_id, {})
            duration = pending.get("duration", "30")
            await license_generate_execute(context, chat_id, message_id, user_id,
                                           duration, quota)

        elif data.startswith("lic_detail_"):
            if not is_super_admin(user_id):
                return
            await license_detail_view(context, chat_id, message_id,
                                      data[len("lic_detail_"):])

        elif data.startswith("lic_extc_"):
            if not is_super_admin(user_id):
                return
            short = data[len("lic_extc_"):]
            rec = await _license_db.find_by_short_hash(short)
            if not rec:
                await license_manager_view(context, chat_id, message_id)
                return
            if rec.effective_status() in (LICENSE_STATUS_LIFETIME, LICENSE_STATUS_REVOKED):
                await license_detail_view(context, chat_id, message_id, short,
                                          banner="⚠️ Cannot be extended.\n\n")
                return
            user_sessions[user_id]["step"] = "wait_extend_days"
            user_sessions[user_id]["lic_short"] = short
            await render(
                context, chat_id, message_id,
                f"✏️ Send the number of days (1-3650) for <code>{html.escape(rec.key_preview)}</code>:",
                [[InlineKeyboardButton("❌ Cancel", callback_data=f"lic_detail_{short}")]],
            )

        elif data.startswith("lic_quota_"):
            if not is_super_admin(user_id):
                return
            short = data[len("lic_quota_"):]
            rec = await _license_db.find_by_short_hash(short)
            if not rec:
                await license_manager_view(context, chat_id, message_id)
                return
            user_sessions[user_id]["step"] = "wait_quota_value"
            user_sessions[user_id]["lic_short"] = short
            await render(
                context, chat_id, message_id,
                f"👥 Send the new max account quota (1-100) for <code>{html.escape(rec.key_preview)}</code>:\n"
                f"Current quota: <b>{rec.max_accounts}</b>",
                [[InlineKeyboardButton("❌ Cancel", callback_data=f"lic_detail_{short}")]],
            )

        elif data.startswith("lic_ext_"):
            if not is_super_admin(user_id):
                return
            rest = data[len("lic_ext_"):].rsplit("_", 1)
            if len(rest) != 2:
                return
            short, days_str = rest
            try:
                days = int(days_str)
            except ValueError:
                return
            await license_extend_execute(context, chat_id, message_id, short, days)

        elif data.startswith("lic_revokeyes_"):
            if not is_super_admin(user_id):
                return
            await license_revoke_execute(context, chat_id, message_id,
                                        data[len("lic_revokeyes_"):], user_id)

        elif data.startswith("lic_revoke_"):
            if not is_super_admin(user_id):
                return
            await license_revoke_confirm(context, chat_id, message_id,
                                        data[len("lic_revoke_"):])

        elif data.startswith("lic_unrev_"):
            if not is_super_admin(user_id):
                return
            await license_unrevoke_execute(context, chat_id, message_id,
                                          data[len("lic_unrev_"):])

        elif data.startswith("lic_delyes_"):
            if not is_super_admin(user_id):
                return
            await license_delete_execute(context, chat_id, message_id,
                                        data[len("lic_delyes_"):])

        elif data.startswith("lic_del_"):
            if not is_super_admin(user_id):
                return
            await license_delete_confirm(context, chat_id, message_id,
                                        data[len("lic_del_"):])

    finally:
        await _safe_answer(query)


# ============================================================================
# Background: license expiry watcher
# ============================================================================

async def license_expiry_watcher(bot_app, config: Config, license_db: LicenseDatabase):
    while True:
        try:
            now = _utcnow()
            for rec in list((await license_db.all()).values()):
                if rec.status == LICENSE_STATUS_REVOKED:
                    continue
                if rec.is_lifetime():
                    continue
                if rec.expiry_notified_at:
                    continue
                if rec.is_expired(now):
                    rec.expiry_notified_at = now.isoformat()
                    rec.touch()
                    await license_db.update(rec)
                    audit_logger.info("license_expired key=%s owner=%s",
                                      rec.key_preview, rec.owner_id)
                    if rec.owner_id:
                        await _notify_license_event(
                            bot_app, config, rec.owner_id,
                            f"⌛ <b>License Expired</b>\n\n"
                            f"Key: <code>{html.escape(rec.key_preview)}</code>\n\n"
                            f"Your bot access has ended.\n"
                            f"Contact admin for renewal.",
                        )
                    await _broadcast_to_admins(
                        bot_app, config,
                        f"⌛ License expired: <code>{html.escape(rec.key_preview)}</code> "
                        f"(owner: <code>{rec.owner_id}</code>)",
                    )
        except Exception as e:
            logger.error("license_expiry_watcher: %s", e)
        await asyncio.sleep(60)


# ============================================================================
# Error handler & bootstrap
# ============================================================================

async def error_handler(update, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    uid = getattr(update, "update_id", "?")

    if isinstance(err, TimedOut):
        logger.warning("TimedOut on update %s (network hiccup, user can retry)", uid)
        return
    if isinstance(err, RetryAfter):
        logger.warning("Rate limited: retry after %ss (update %s)", err.retry_after, uid)
        return
    if isinstance(err, NetworkError):
        logger.warning("NetworkError on update %s: %s", uid, err)
        return

    logger.error("Update %s caused error: %s", uid, err, exc_info=err)


def make_post_init(session_manager: SessionManager):
    async def post_init(application: Application):
        loaded = await _license_db.load()
        logger.info("Connected to MongoDB (PyMongo). Loaded %d license(s).", loaded)
        await session_manager.load_all()
        session_manager.track(asyncio.create_task(session_manager.health_check_loop()))
        session_manager.track(asyncio.create_task(user_session_sweeper(application.bot)))
        if _license_db is not None:
            session_manager.track(asyncio.create_task(
                license_expiry_watcher(application.bot, session_manager.config, _license_db)
            ))
        me = await application.bot.get_me()
        lic_count = len(await _license_db.all()) if _license_db else 0
        banner = (
            "\n" + "=" * 46 + "\n"
            f"  Anti-Login Bot running as @{me.username}\n"
            f"  Protected accounts : {len(await session_manager.phones())}\n"
            f"  Registered admins  : {len(session_manager.config.admin_ids)}\n"
            f"  Licenses loaded    : {lic_count}\n"
            + "=" * 46
        )
        logger.info(banner)
    return post_init


def make_post_shutdown(session_manager: SessionManager):
    async def post_shutdown(application: Application):
        await session_manager.shutdown()
    return post_shutdown


def main():
    global _config, _session_manager, _license_db

    config = load_config(Path(CONFIG_FILE))
    if config is None:
        return
    _config = config

    if not config.admin_ids:
        logger.warning("No admin_ids configured — alerts will not be delivered.")

    _license_db = LicenseDatabase(
        config.mongo_uri,
        config.license_salt,
        config.db_name)

    database = AccountDatabase(config.mongo_uri, config.db_name)
    session_manager = SessionManager(config, database)
    _session_manager = session_manager

    general_request = HTTPXRequest(
        connection_pool_size=16,
        connect_timeout=10.0,
        read_timeout=30.0,
        write_timeout=30.0,
        pool_timeout=5.0,
    )
    get_updates_request = HTTPXRequest(
        connection_pool_size=1,
        connect_timeout=15.0,
        read_timeout=60.0,
        write_timeout=30.0,
        pool_timeout=10.0,
    )
    bot_app = (
        Application.builder()
        .token(config.bot_token)
        .request(general_request)
        .get_updates_request(get_updates_request)
        .rate_limiter(AIORateLimiter(max_retries=3))
        .post_init(make_post_init(session_manager))
        .post_shutdown(make_post_shutdown(session_manager))
        .build()
    )
    session_manager.bot_app = bot_app

    bot_app.add_handler(CommandHandler("start", start_command))
    bot_app.add_handler(CommandHandler("cancel", cancel_command))
    bot_app.add_handler(CallbackQueryHandler(button_callback))
    bot_app.add_handler(
        MessageHandler(
            filters.TEXT & ~filters.COMMAND,
            message_handler))
    bot_app.add_error_handler(error_handler)

    logger.info("Starting bot...")
    try:
        bot_app.run_polling(allowed_updates=Update.ALL_TYPES)
    except Exception as e:
        logger.exception("Bot terminated with error: %s", e)
        raise


if __name__ == "__main__":
    main()