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
    def __init__(self, path: Path, salt: str, backup_count: int = 1):
        self.path = path
        self.salt = salt
        self.backup_dir = path.parent / "backups"
        self.backup_count = backup_count
        self._records: dict[str, LicenseRecord] = {}
        self._owner_index: dict[int, str] = {}
        self._last_backup = 0.0

    def load(self) -> int:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        raw = self._read_with_recovery()
        self._records.clear()
        self._owner_index.clear()
        count = 0
        for key_hash, data in raw.items():
            err = validate_license_record(data)
            if err:
                log.warning("Rejected license record %s: %s", key_hash[:8], err)
                continue
            try:
                rec = LicenseRecord.from_dict(data)
            except Exception as e:
                log.error("Failed to parse license %s: %s", key_hash[:8], e)
                continue
            self._records[key_hash] = rec
            if rec.owner_id is not None:
                self._owner_index[rec.owner_id] = key_hash
            count += 1
        return count

    def _read_with_recovery(self) -> dict:
        if not self.path.exists():
            return {}
        try:
            content = self.path.read_text(encoding="utf-8")
            if not content.strip():
                return {}
            data = json.loads(content)
            if not isinstance(data, dict):
                raise ValueError("not a dict")
            return data
        except Exception as e:
            log.error("licenses.json corrupt (%s). Trying backups.", e)
            return self._recover_from_backup()

    def _recover_from_backup(self) -> dict:
        backups = sorted(self.backup_dir.glob("licenses_*.json"), reverse=True)
        for b in backups:
            try:
                data = json.loads(b.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    log.warning("Recovered licenses from %s", b.name)
                    return data
            except Exception:
                continue
        return {}

    def all(self) -> dict:
        return dict(self._records)

    def get_by_hash(self, key_hash: str) -> Optional[LicenseRecord]:
        return self._records.get(key_hash)

    def get_by_owner(self, owner_id: int) -> Optional[LicenseRecord]:
        h = self._owner_index.get(owner_id)
        return self._records.get(h) if h else None

    def find_by_plaintext(self, key: str) -> Optional[LicenseRecord]:
        return self._records.get(hash_key(key, self.salt))

    def find_by_short_hash(self, short: str) -> Optional[LicenseRecord]:
        if not short:
            return None
        for h, r in self._records.items():
            if h.startswith(short):
                return r
        return None

    def add(self, record: LicenseRecord) -> None:
        self._records[record.key_hash] = record
        if record.owner_id is not None:
            self._owner_index[record.owner_id] = record.key_hash
        self._save()

    def update(self, record: LicenseRecord) -> None:
        self._records[record.key_hash] = record
        self._owner_index = {
            r.owner_id: h for h, r in self._records.items() if r.owner_id is not None
        }
        self._save()

    def delete(self, key_hash: str) -> bool:
        if key_hash not in self._records:
            return False
        rec = self._records.pop(key_hash)
        if rec.owner_id and self._owner_index.get(rec.owner_id) == key_hash:
            del self._owner_index[rec.owner_id]
        self._save()
        return True

    def _save(self) -> None:
        data = {h: r.to_dict() for h, r in self._records.items()}
        self.path.parent.mkdir(parents=True, exist_ok=True)
        tmp = self.path.with_suffix(".tmp")
        try:
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, self.path)
        except Exception as e:
            log.error("Failed to save licenses.json: %s", e)
            return
        self._rotate_backup(data)

    def _rotate_backup(self, data: dict) -> None:
        now = time.monotonic()
        if now - self._last_backup < BACKUP_MIN_INTERVAL_SECONDS:
            return
        self._last_backup = now
        stamp = _utcnow().strftime("%Y%m%dT%H%M%S%f")
        try:
            (self.backup_dir / f"licenses_{stamp}.json").write_text(
                json.dumps(data, indent=2, ensure_ascii=False), encoding="utf-8"
            )
            backups = sorted(self.backup_dir.glob("licenses_*.json"))
            for stale in backups[: -self.backup_count]:
                stale.unlink()
        except Exception:
            pass