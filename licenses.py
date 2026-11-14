from __future__ import annotations

import dataclasses
import hashlib
import json
import logging
import os
import secrets
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Optional

log = logging.getLogger("anti_login")

KEY_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
KEY_PREFIX = "AL"
KEY_SEGMENTS = 4
KEY_SEGMENT_LEN = 4
KEY_CHECKSUM_LEN = 2

LICENSE_STATUS_ACTIVE = "active"
LICENSE_STATUS_EXPIRED = "expired"
LICENSE_STATUS_REVOKED = "revoked"
LICENSE_STATUS_LIFETIME = "lifetime"

BACKUP_MIN_INTERVAL_SECONDS = 60


def _utcnow() -> datetime:
    return datetime.now(timezone.utc).replace(tzinfo=None)


def _gen_segment() -> str:
    return "".join(secrets.choice(KEY_ALPHABET) for _ in range(KEY_SEGMENT_LEN))


def _checksum(payload: str) -> str:
    h = hashlib.sha256(payload.encode()).digest()
    return "".join(KEY_ALPHABET[b % 32] for b in h[:2])


def generate_key() -> str:
    segments = [_gen_segment() for _ in range(KEY_SEGMENTS)]
    payload = "-".join(segments)
    return f"{KEY_PREFIX}-{payload}-{_checksum(payload)}"


def normalize_key(key: str) -> Optional[str]:
    if not key:
        return None
    cleaned = key.strip().upper().replace(" ", "").replace("-", "")
    if not cleaned.startswith(KEY_PREFIX):
        return None
    body = cleaned[len(KEY_PREFIX):]
    expected = KEY_SEGMENTS * KEY_SEGMENT_LEN + KEY_CHECKSUM_LEN
    if len(body) != expected:
        return None
    if not all(c in KEY_ALPHABET for c in body):
        return None
    payload = body[: KEY_SEGMENTS * KEY_SEGMENT_LEN]
    cs = body[KEY_SEGMENTS * KEY_SEGMENT_LEN:]
    segs = [payload[i:i + KEY_SEGMENT_LEN] for i in range(0, len(payload), KEY_SEGMENT_LEN)]
    if _checksum("-".join(segs)) != cs:
        return None
    return f"{KEY_PREFIX}-{'-'.join(segs)}-{cs}"


def mask_key(key: str) -> str:
    if not key:
        return "AL-••••-••••-••••-••••-••"
    parts = key.split("-")
    if len(parts) < 3:
        return "AL-••••-••••-••••-••••-" + key[-2:]
    masked = ["•" * len(p) for p in parts[1:-1]]
    return f"{parts[0]}-{'-'.join(masked)}-{parts[-1]}"


def hash_key(key: str, salt: str) -> str:
    return hashlib.sha256((salt + ":" + key).encode()).hexdigest()


@dataclasses.dataclass
class LicenseRecord:
    key_hash: str
    key_preview: str
    owner_id: Optional[int] = None
    status: str = LICENSE_STATUS_ACTIVE
    max_accounts: int = 3
    created_at: str = dataclasses.field(default_factory=lambda: _utcnow().isoformat())
    updated_at: str = dataclasses.field(default_factory=lambda: _utcnow().isoformat())
    expires_at: Optional[str] = None
    redeemed_at: Optional[str] = None
    revoked_at: Optional[str] = None
    revoked_by: Optional[int] = None
    revoke_reason: Optional[str] = None
    created_by: Optional[int] = None
    note: Optional[str] = None
    expiry_notified_at: Optional[str] = None

    def touch(self) -> None:
        self.updated_at = _utcnow().isoformat()

    def is_lifetime(self) -> bool:
        return self.expires_at is None

    def is_expired(self, now: Optional[datetime] = None) -> bool:
        if self.expires_at is None:
            return False
        now = now or _utcnow()
        try:
            return datetime.fromisoformat(self.expires_at) <= now
        except ValueError:
            return True

    def effective_status(self, now: Optional[datetime] = None) -> str:
        if self.status == LICENSE_STATUS_REVOKED:
            return LICENSE_STATUS_REVOKED
        if self.is_expired(now):
            return LICENSE_STATUS_EXPIRED
        if self.is_lifetime():
            return LICENSE_STATUS_LIFETIME
        return LICENSE_STATUS_ACTIVE

    def is_usable(self, now: Optional[datetime] = None) -> bool:
        return self.effective_status(now) in (LICENSE_STATUS_ACTIVE, LICENSE_STATUS_LIFETIME)

    def to_dict(self) -> dict:
        return dataclasses.asdict(self)

    @staticmethod
    def from_dict(d: dict) -> "LicenseRecord":
        names = {f.name for f in dataclasses.fields(LicenseRecord)}
        return LicenseRecord(**{k: v for k, v in d.items() if k in names})


def validate_license_record(data) -> Optional[str]:
    if not isinstance(data, dict):
        return "not a dict"
    if not isinstance(data.get("key_hash"), str) or not data["key_hash"]:
        return "missing key_hash"
    if not isinstance(data.get("key_preview"), str):
        return "missing key_preview"
    owner = data.get("owner_id")
    if owner is not None and (not isinstance(owner, int) or isinstance(owner, bool)):
        return "owner_id must be int or null"
    ma = data.get("max_accounts")
    if not isinstance(ma, int) or isinstance(ma, bool) or ma < 1:
        return "invalid max_accounts"
    return None


class LicenseDatabase:
    def __init__(self, mongo_uri: str, salt: str, db_name: str = "anti_login_bot"):
        from pymongo import AsyncMongoClient
        self.client = AsyncMongoClient(mongo_uri)
        self.db = self.client[db_name]
        self.collection = self.db["licenses"]
        self.salt = salt

    async def load(self) -> int:
        await self.collection.create_index("key_hash", unique=True)
        await self.collection.create_index("owner_id")
        count = await self.collection.count_documents({})
        return count

    def _to_record(self, data: dict) -> LicenseRecord:
        data.pop("_id", None)
        return LicenseRecord(**data)

    async def add(self, record: LicenseRecord):
        await self.collection.insert_one(dataclasses.asdict(record))

    async def update(self, record: LicenseRecord):
        record.touch()
        await self.collection.update_one(
            {"key_hash": record.key_hash},
            {"$set": dataclasses.asdict(record)}
        )

    async def delete(self, key_hash: str):
        await self.collection.delete_one({"key_hash": key_hash})

    async def all(self) -> dict:
        cursor = self.collection.find({})
        records = {}
        async for data in cursor:
            rec = self._to_record(data)
            records[rec.key_hash] = rec
        return records

    async def get_by_owner(self, owner_id: int) -> Optional[LicenseRecord]:
        data = await self.collection.find_one({"owner_id": owner_id})
        return self._to_record(data) if data else None

    async def find_by_short_hash(self, short: str) -> Optional[LicenseRecord]:
        data = await self.collection.find_one({"key_hash": {"$regex": f"^{short}"}})
        return self._to_record(data) if data else None

    async def find_by_plaintext(self, plaintext: str) -> Optional[LicenseRecord]:
        key_hash = hash_key(plaintext, self.salt)
        data = await self.collection.find_one({"key_hash": key_hash})
        return self._to_record(data) if data else None

