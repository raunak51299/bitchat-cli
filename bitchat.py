#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
bitchat CLI — internet mode, wire-compatible with the OFFICIAL bitchat app.

Speaks the same protocol as the mobile app's internet mode (see
permissionlesstech/bitchat-android), so a phone running the real bitchat app and
this CLI can meet in the same location ("geohash") channels:

  * channels are geohash location channels over Nostr relays
      kind 20000  = geochat message    (plaintext content, tags g=<geohash>, n=<nick>)
      kind 20001  = presence heartbeat (empty content, tag g=<geohash>)
  * events are standard Nostr (NIP-01), signed BIP-340 schnorr
  * identity is per-geohash, derived exactly like the app:
        key_i = HMAC-SHA256(seed, geohash || LE32(i))   i = 0..9, first valid
        fallback: SHA-256(seed || geohash)
  * relays: the 5 relays from the app's georelays CSV nearest to the geohash
  * DMs (kind 1059 gift wraps): NOT supported here — the official app
    tunnel-encrypts them with mesh-Noise sessions on top. Public geochat is what
    phones use to talk openly, and that is exactly what this CLI does.

Run:   python bitchat.py            (then  /help)
"""

import argparse
import asyncio
import base64
import concurrent.futures
import hashlib
import hmac
import json
import math
import os
import random
import re
import secrets
import shutil
import struct
import sys
import threading
import time
from collections import deque
from pathlib import Path

try:
    import websockets
except ImportError:
    print("missing dependency: pip install websockets", file=sys.stderr)
    raise SystemExit(1)

sys.stdout.reconfigure(encoding="utf-8", errors="replace")
sys.stderr.reconfigure(encoding="utf-8", errors="replace")

import secp  # local BIP-340 implementation (validated against official vectors)

# ---------------------------------------------------------------- constants
APP_DIR          = Path.home() / ".bitchat-cli"
NOSTR_STATE_FILE = APP_DIR / "nostr.json"          # device seed + prefs
LEGACY_FILE      = APP_DIR / "identity.json"       # old custom-protocol client file

GEORELAYS_URL = ("https://raw.githubusercontent.com/"
                 "permissionlesstech/georelays/refs/heads/main/nostr_relays.csv")
APP_DEFAULT_RELAYS = [
    "wss://relay.damus.io",
    "wss://relay.primal.net",
    "wss://offchain.pub",
    "wss://nostr21.com",
]

N_RELAYS           = 5      # the app connects to the 5 nearest relays per geohash
KIND_MSG           = 20000  # geohash chat message
KIND_PRESENCE      = 20001  # geohash presence heartbeat
PRESENCE_MIN_S     = 40.0   # app heartbeat window (foreground): 40..80 s
PRESENCE_MAX_S     = 80.0
PARTICIPANT_TTL_S  = 300    # app prunes participants not seen for 5 minutes
SUB_BACKLOG_SINCE  = 3600   # app asks for the last hour, limit 200
SUB_BACKLOG_LIMIT  = 200
RECONNECT_BACKLOG_S = 120   # a reconnect replays at most this gap - not a
                            # full hour of backlog after every relay flap
FUTURE_SLACK_S     = 90     # tolerate clock skew on incoming created_at
MAX_NICK_LEN       = 15     # UI.MAX_NICKNAME_LENGTH in the app
MAX_TEXT_LEN       = 1000

C = "\x1b["
def _c(code: str, s: str) -> str:
    return f"{C}{code}m{s}{C}0m" if sys.stdout.isatty() else s

def dim(s):    return _c("90", s)
def green(s):  return _c("32", s)
def yellow(s): return _c("33", s)
def red(s):    return _c("31", s)
def cyan(s):   return _c("36", s)
def bold(s):   return _c("1", s)

# --- output row tracking ------------------------------------------------
# Our own message shows a status dot: ● yellow = sending, ● green = relayed.
# When a relay confirms, we jump the cursor back to that dot and recolor it
# in place. That needs to know how many screen rows were printed since, so
# every interactive output goes through log().
_ANSI_RE = re.compile("\x1b\\[[0-9;?]*[A-Za-z]")

def _plain(s: str) -> str:
    return _ANSI_RE.sub("", s)

def _wide(o: int) -> bool:
    """East-Asian Wide / emoji: occupy two terminal columns."""
    return (0x1100 <= o <= 0x115F or 0x2E80 <= o <= 0xA4CF
            or 0xAC00 <= o <= 0xD7A3 or 0xF900 <= o <= 0xFAFF
            or 0xFE10 <= o <= 0xFE19 or 0xFE30 <= o <= 0xFE6F
            or 0xFF00 <= o <= 0xFF60 or 0xFFE0 <= o <= 0xFFE6
            or 0x1F300 <= o <= 0x1F9FF or 0x1FA70 <= o <= 0x1FAFF
            or 0x20000 <= o <= 0x3FFFD)

def _vis_len(s: str) -> int:
    """Display width: emoji/CJK count 2 columns, ZWJ/variation selectors
    count 0. Naive wcwidth, good enough for row math."""
    n = 0
    for ch in s:
        o = ord(ch)
        if 0x0300 <= o <= 0x036F or o in (0x00AD, 0x200B, 0x200C, 0x200D,
                                         0xFE0E, 0xFE0F):
            continue
        n += 2 if _wide(o) else 1
    return n

def _wrap_ansi(s: str, width: int) -> list:
    """ANSI-aware greedy wrap for the alternate-screen pane. SGR sequences
    are carried along unmeasured; CJK/emoji count double."""
    if _vis_len(s) <= width:
        return [s]
    lines, cur, w = [], "", 0
    i, n = 0, len(s)
    while i < n:
        if s[i] == "\x1b":
            m = _ANSI_RE.match(s, i)
            if m:
                cur += m.group(0)
                i = m.end()
                continue
        ch = s[i]
        cw = 2 if _wide(ord(ch)) else 1
        if w + cw > width:
            lines.append(cur)
            cur, w = "", 0
            if ch == " ":
                i += 1
                continue
        cur += ch
        w += cw
        i += 1
    if cur:
        lines.append(cur)
    return lines or [""]

def _term_cols() -> int:
    return max(10, shutil.get_terminal_size((80, 24)).columns)

def _rows(s: str) -> int:
    cols = _term_cols()
    total = 0
    for part in _plain(s).split("\n"):
        total += max(1, -(-_vis_len(part) // cols))
    return total

_cursor_rows = [0]          # console rows emitted by log() so far

def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    _cursor_rows[0] += _rows(s)

def sysline(s): log(_c("90", s))

VERBOSE = False                     # set from --verbose in main()


def _dbg(msg: str):
    """Breadcrumb for best-effort (exception-swallowing) paths. Silent
    unless --verbose; these paths keep the client running on purpose."""
    if VERBOSE:
        log(dim("   · " + msg))


# ---------------------------------------------------------------- geohash
_B32 = "0123456789bcdefghjkmnpqrstuvwxyz"
_B32V = {ch: i for i, ch in enumerate(_B32)}

def geohash_encode(lat: float, lon: float, precision: int) -> str:
    if precision <= 0:
        return ""
    lat = max(-90.0, min(90.0, float(lat)))
    lon = max(-180.0, min(180.0, float(lon)))
    latlo, lathi = -90.0, 90.0
    lonlo, lonhi = -180.0, 180.0
    even, bit, ch = True, 0, 0
    out = []
    while len(out) < precision:
        if even:
            mid = (lonlo + lonhi) / 2
            if lon >= mid:
                ch |= (1 << (4 - bit)); lonlo = mid
            else:
                lonhi = mid
        else:
            mid = (latlo + lathi) / 2
            if lat >= mid:
                ch |= (1 << (4 - bit)); latlo = mid
            else:
                lathi = mid
        even = not even
        if bit < 4:
            bit += 1
        else:
            out.append(_B32[ch]); bit = 0; ch = 0
    return "".join(out)

def geohash_bounds(gh: str):
    latlo, lathi = -90.0, 90.0
    lonlo, lonhi = -180.0, 180.0
    even = True
    for ch in gh.lower():
        cd = _B32V.get(ch)
        if cd is None:
            raise ValueError("invalid geohash")
        for mask in (16, 8, 4, 2, 1):
            if even:
                mid = (lonlo + lonhi) / 2
                if cd & mask: lonlo = mid
                else:         lonhi = mid
            else:
                mid = (latlo + lathi) / 2
                if cd & mask: latlo = mid
                else:         lathi = mid
            even = not even
    return latlo, lathi, lonlo, lonhi

def geohash_center(gh: str):
    latlo, lathi, lonlo, lonhi = geohash_bounds(gh)
    return (latlo + lathi) / 2, (lonlo + lonhi) / 2

def geohash_level_name(gh: str) -> str:
    return {8: "building", 7: "block", 6: "neighborhood",
            5: "city", 4: "province", 2: "region",
            9: "building", 10: "block"}.get(len(gh), f"custom({len(gh)})")

# ---------------------------------------------------------------- bech32 (npub)
_B32_BECH = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
_BECH32V = {ch: i for i, ch in enumerate(_B32_BECH)}

def _bech32_polymod(values) -> int:
    gen = [0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3]
    chk = 1
    for v in values:
        top = chk >> 25
        chk = ((chk & 0x1FFFFFF) << 5) ^ v
        for i, g in enumerate(gen):
            if (top >> i) & 1:
                chk ^= g
    return chk

def _bech32_hrp_expand(hrp):
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]

def _convertbits(data, frombits, tobits, pad=True):
    acc, bits, ret = 0, 0, []
    maxv = (1 << tobits) - 1
    for value in data:
        acc = (acc << frombits) | value
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad and bits:
        ret.append((acc << (tobits - bits)) & maxv)
    return ret

def npub_encode(pub_hex: str) -> str:
    data = _convertbits(bytes.fromhex(pub_hex), 8, 5, True)
    hrp = "npub"
    values = _bech32_hrp_expand(hrp) + data
    poly = _bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    checksum = [(poly >> 5 * (5 - i)) & 31 for i in range(6)]
    return hrp + "1" + "".join(_B32_BECH[d] for d in data + checksum)

def npub_decode(npub: str) -> str:
    npub = npub.strip().lower()
    if not npub.startswith("npub1"):
        raise ValueError("not a npub")
    values = []
    for ch in npub[5:]:
        if ch not in _BECH32V:
            raise ValueError("bad bech32 character")
        values.append(_BECH32V[ch])
    hrps = _bech32_hrp_expand("npub")
    if _bech32_polymod(hrps + values) != 1:
        raise ValueError("bad bech32 checksum")
    return bytes(_convertbits(values[:-6], 5, 8, False)).hex()

# ---------------------------------------------------------------- identity
class Identity:
    """Device seed + per-geohash derived Nostr identities (app's exact scheme)."""

    def __init__(self, seed: bytes, nick: str = ""):
        assert isinstance(seed, bytes) and len(seed) == 32
        self.seed = seed
        self.nick = nick[:MAX_NICK_LEN]
        self._cache = {}
        self.state = {}

    @classmethod
    def load_or_create(cls) -> "Identity":
        APP_DIR.mkdir(parents=True, exist_ok=True)
        state = {}
        if NOSTR_STATE_FILE.exists():
            try:
                state = json.loads(NOSTR_STATE_FILE.read_text(encoding="utf-8"))
            except Exception as e:
                _dbg(f"identity file unreadable, starting fresh: {e}")
                state = {}
        seed = secrets.token_bytes(32)
        if state.get("seed"):
            try:
                cand = base64.b64decode(state["seed"])
                if len(cand) == 32:
                    seed = cand
            except Exception as e:
                _dbg(f"stored seed b64 invalid, new identity: {e}")
        nick = state.get("nick") or ""
        if not nick:
            nick = "anon" + hashlib.sha256(seed + b"nick").hexdigest()[:4]
            try:
                if LEGACY_FILE.exists():
                    nick = (json.loads(LEGACY_FILE.read_text(encoding="utf-8"))
                            .get("nick") or nick)
            except Exception as e:
                _dbg(f"legacy nick file unread: {e}")
            nick = nick[:MAX_NICK_LEN]
        ident = cls(seed, nick)
        ident.state = state
        return ident

    def save(self, geohash: str | None = None):
        try:
            self.state.update({
                "seed": base64.b64encode(self.seed).decode("ascii"),
                "nick": self.nick,
                "geohash": geohash if geohash is not None
                           else self.state.get("geohash"),
                "updated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            })
            NOSTR_STATE_FILE.write_text(
                json.dumps(self.state, indent=2) + "\n", encoding="utf-8")
        except Exception as e:
            sysline(f"(could not save state: {e})")

def hashlash(seed: bytes, ghb: bytes) -> bytes:
    """Per-geohash fallback derivation; keeps rehashing until a valid key."""
    salt = 0
    while True:
        cand = hashlib.sha256(seed + ghb + salt.to_bytes(4, "little")).digest()
        if 0 < int.from_bytes(cand, "big") < secp.N:
            return cand
        salt += 1

def derive_seed_priv(seed: bytes, geohash: str) -> bytes:
    """App's NostrIdentityBridge.deriveIdentity as a standalone function."""
    ghb = geohash.lower().encode("utf-8")
    for i in range(10):
        cand = hmac.new(seed, ghb + struct.pack("<I", i), hashlib.sha256).digest()
        if 0 < int.from_bytes(cand, "big") < secp.N:
            return cand
    return hashlash(seed, ghb)

# ---------------------------------------------------------------- nostr events
def event_id(pub_hex: str, created_at: int, kind: int, tags, content: str):
    """NIP-01 event id: sha256 over compact JSON [0,pub,created_at,kind,tags,content]."""
    payload = json.dumps([0, pub_hex, created_at, kind, tags, content],
                         separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).digest()

def sign_event(priv_hex: str, kind: int, tags, content: str,
               created_at: int | None = None) -> dict:
    priv = bytes.fromhex(priv_hex)
    pub_hex = secp.pubkey_xonly(priv)[0].hex()
    if created_at is None:
        created_at = int(time.time())
    idhash = event_id(pub_hex, created_at, kind, tags, content)
    sig = secp.sign(priv, idhash)
    return {
        "id": idhash.hex(),
        "pubkey": pub_hex,
        "created_at": created_at,
        "kind": kind,
        "tags": tags,
        "content": content,
        "sig": sig.hex(),
    }

def pow_bits(id_hex: str) -> int:
    """Leading zero bits of an event id (NIP-13 difficulty)."""
    bits = 0
    for ch in id_hex:
        v = int(ch, 16)
        if v == 0:
            bits += 4
        else:
            bits += 4 - v.bit_length()
            break
    return bits

def nip13_mine(priv_hex: str, ev: dict, difficulty: int) -> dict | None:
    """NIP-13 proof-of-work: find a nonce tag so the event id has at least
    `difficulty` leading zero bits, then re-sign. Runs in a worker thread
    (pure-Python: ~2**d id hashes, i.e. d=20 ~ several seconds)."""
    if not (8 <= difficulty <= 24):
        return None
    tags = [list(t) for t in ev.get("tags", [])]
    pub_hex = ev["pubkey"]
    created_at = ev["created_at"]
    kind = ev["kind"]
    content = ev["content"]
    for nonce in range(1 << 30):
        t2 = tags + [["nonce", str(nonce), str(difficulty)]]
        eid = event_id(pub_hex, created_at, kind, t2, content)
        if pow_bits(eid.hex()) >= difficulty:
            return sign_event(priv_hex, kind, t2, content, created_at)
    return None

def verify_event(ev: dict, geohash: str | None) -> bool:
    """App-style validation: id match + schnorr sig + (client-side) g-tag filter."""
    try:
        if ev.get("kind") not in (KIND_MSG, KIND_PRESENCE):
            return False
        if geohash is not None and tag_value(ev, "g") != geohash.lower():
            return False
        pub = ev["pubkey"].lower()
        tags = ev.get("tags")
        if not isinstance(tags, list):
            return False
        created = int(ev["created_at"])
        kind = int(ev["kind"])
        content = ev.get("content", "")
        ev_id = event_id(pub, created, kind, tags, content)
        if ev_id.hex() != ev.get("id"):
            return False
        return secp.verify(bytes.fromhex(pub), ev_id, bytes.fromhex(ev["sig"]))
    except Exception:
        return False

def tag_value(ev: dict, name: str):
    tags = ev.get("tags") or []
    if isinstance(tags, list):
        for t in tags:
            if isinstance(t, (list, tuple)) and len(t) >= 2 and t[0] == name:
                return t[1]
    return None

# ---------------------------------------------------------------- DMs
# Official-app private messages ride the geochat relays as kind 1059 gift
# wraps ("NIP-17") addressed to our per-geohash key: 1059 -> kind 13 seal ->
# unsigned kind 14 rumor, whose content is "bitchat1:" + base64url of a
# mesh BitchatPacket (type NOISE_ENCRYPTED=0x11) - a mesh-Noise session blob.
# Encryption quirk (matches iOS): HKDF input is the 33-byte COMPRESSED shared
# point, AEAD is XChaCha20-Poly1305 with a 24-byte nonce, base64url no pad.
#
# The CLI fully unwraps the envelope (so a DM shows: who, when, what type).
# The Noise-session body itself cannot be opened here: session state only
# exists on phones after BLE handshakes, so DM text stays readable on phones.

def _hkdf_sha256(salt: bytes, ikm: bytes, info: bytes, n: int = 32) -> bytes:
    """RFC 5869 HKDF-SHA256 (bitchat/iOS derive: extract salt=b'', info nip44)."""
    prk = hmac.new(salt or b"\x00" * 32, ikm, hashlib.sha256).digest()
    okm, t, i = b"", b"", 1
    while len(okm) < n:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        okm += t
        i += 1
    return okm[:n]

def _rotl(v, n):
    return ((v << n) | (v >> (32 - n))) & 0xFFFFFFFF

def _hchacha20(key: bytes, nonce16: bytes) -> bytes:
    """HChaCha20 (libsodium construction): XChaCha's subkey derivation."""
    import struct
    assert len(key) == 32 and len(nonce16) == 16
    state = [0x61707865, 0x3320646E, 0x79622D32, 0x6B206574,
             *struct.unpack("<8I", key), *struct.unpack("<4I", nonce16)]

    def qr(x, a, b, c, d):
        x[a] = (x[a] + x[b]) & 0xFFFFFFFF
        x[d] = _rotl(x[d] ^ x[a], 16)
        x[c] = (x[c] + x[d]) & 0xFFFFFFFF
        x[b] = _rotl(x[b] ^ x[c], 12)
        x[a] = (x[a] + x[b]) & 0xFFFFFFFF
        x[d] = _rotl(x[d] ^ x[a], 8)
        x[c] = (x[c] + x[d]) & 0xFFFFFFFF
        x[b] = _rotl(x[b] ^ x[c], 7)

    for _ in range(10):
        for a, b, c, d in ((0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14),
                           (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12),
                           (2, 7, 8, 13), (3, 4, 9, 14)):
            qr(state, a, b, c, d)
    return struct.pack("<8I", *(state[:4] + state[12:16]))

def _nip44_quirk_decrypt(content: str, sender_pub_hex: str,
                         recipient_priv_hex: str) -> str:
    """bitchat/iOS 'v2:' NIP-44: compressed-point HKDF + XChaCha20-Poly1305.
    Tries even-Y parity first, then odd-Y (same order as the app)."""
    if not content.startswith("v2:"):
        raise ValueError("not v2: content")
    blob = _b64url_decode(content[3:])
    priv = bytes.fromhex(recipient_priv_hex[-64:])
    peer = bytes.fromhex(sender_pub_hex)[-32:]
    last = None
    for odd in (False, True):
        shared = secp.ecdh_compressed(priv, peer, odd)
        if shared is None:
            continue
        try:
            return _xchacha_poly_decrypt(_hkdf_sha256(b"", shared,
                                                      b"nip44-v2"), blob) \
                .decode("utf-8")
        except Exception as e:
            last = e
    raise ValueError(f"nip44 decrypt failed: {last}")

def nip44_quirk_encrypt(plaintext: str, recipient_pub_hex: str,
                        sender_priv_hex: str) -> str:
    """Inverse of _nip44_quirk_decrypt (same quirk, even-Y like the app)."""
    shared = secp.ecdh_compressed(bytes.fromhex(sender_priv_hex[-64:]),
                                  bytes.fromhex(recipient_pub_hex)[-32:],
                                  False)
    if shared is None:
        raise ValueError("bad recipient key")
    blob = _xchacha_poly_encrypt(_hkdf_sha256(b"", shared, b"nip44-v2"),
                                 plaintext.encode("utf-8"))
    return "v2:" + _b64url_encode(blob)

def _b64url_encode(b: bytes) -> str:
    import base64
    return base64.urlsafe_b64encode(b).decode("ascii").rstrip("=")

def _b64url_decode(s: str) -> bytes:
    import base64
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))

def _xchacha_poly_decrypt(key: bytes, blob: bytes, aad: bytes = b"") -> bytes:
    nonce24, data = blob[:24], blob[24:]
    subkey = _hchacha20(key, nonce24[:16])
    n12 = b"\x00" * 4 + nonce24[16:24]      # 4 NULs + 8B tail = 12B (draft 2.3)
    return _aead(subkey).decrypt(n12, data, aad or None)

def _xchacha_poly_encrypt(key: bytes, plaintext: bytes,
                          aad: bytes = b"") -> bytes:
    nonce24 = secrets.token_bytes(24)
    subkey = _hchacha20(key, nonce24[:16])
    n12 = b"\x00" * 4 + nonce24[16:24]
    return nonce24 + _aead(subkey).encrypt(n12, plaintext, aad or None)

def _aead(subkey: bytes):
    from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
    return ChaCha20Poly1305(subkey)

def _valid_seal(seal: dict) -> bool:
    """kind 13 seal JSON must verify like any Nostr event (app checks sig)."""
    try:
        eid = event_id(seal["pubkey"], int(seal["created_at"]),
                       int(seal["kind"]), seal["tags"], seal["content"])
        return eid.hex() == seal.get("id") and secp.verify(
            bytes.fromhex(seal["pubkey"][-64:]), eid,
            bytes.fromhex(seal.get("sig") or ""))
    except Exception:
        return False

def dm_open_gift(gift: dict, recipient_priv_hex: str) -> dict | None:
    """1059 gift wrap -> kind 13 seal (verified) -> kind 14 rumor dict."""
    try:
        seal = json.loads(_nip44_quirk_decrypt(
            gift["content"], gift["pubkey"], recipient_priv_hex))
        if not isinstance(seal, dict) or int(seal.get("kind", 0)) != 13:
            return None
        if not _valid_seal(seal):
            return None
        rumor = json.loads(_nip44_quirk_decrypt(
            seal["content"], seal["pubkey"], recipient_priv_hex))
    except Exception:
        return None
    if not isinstance(rumor, dict) or int(rumor.get("kind", 0)) != 14:
        return None
    return rumor

def parse_bitchat_packet(content: str) -> dict | None:
    """Header parse of the rumor's 'bitchat1:' base64url mesh packet.
    Only enough fields to classify; the Noise payload stays opaque."""
    if not content.startswith("bitchat1:"):
        return None
    try:
        raw = _b64url_decode(content[len("bitchat1:"):])
    except Exception:
        return None
    data = raw
    if data:
        pad = data[-1]
        if 1 <= pad <= min(255, len(data)) and \
                data[-pad:] == bytes([pad]) * pad:
            data = data[:-pad]                      # trailing PKCS#7-ish pad
    if len(data) < 26:
        return None
    version = data[0]
    if version not in (1, 2):
        return None
    ptype = data[1]
    ttl = data[2]
    ts_ms = int.from_bytes(data[3:11], "big")
    flags = data[11]
    has_recipient = bool(flags & 0x01)
    if version == 1:
        plen = int.from_bytes(data[12:14], "big")
        hdr = 14
    else:
        plen = int.from_bytes(data[12:16], "big")
        hdr = 16
    off = hdr + 8                                  # sender id (8 bytes)
    sender_id = data[hdr:off]
    if has_recipient:
        off += 8                                   # recipient id
    if flags & 0x08:                               # v2 source route
        if off < len(data):
            route_count = data[off]
            off += 1 + route_count * 8
    payload = data[off:]
    if flags & 0x04:                               # deflate-compressed payload
        import zlib
        try:
            payload = zlib.decompressobj(-15).decompress(payload)
        except Exception:
            return None
    else:
        payload = payload[:plen]
    names = {0x01: "announce", 0x02: "message", 0x03: "leave",
             0x10: "noise-handshake", 0x11: "noise-encrypted",
             0x20: "fragment", 0x21: "sync-request",
             0x22: "file-transfer", 0x29: "voice"}
    return {"version": version, "type": ptype,
            "type_name": names.get(ptype, f"unknown(0x{ptype:02x})"),
            "ttl": ttl, "ts_ms": ts_ms, "sender_id": sender_id.hex(),
            "payload_len": len(payload)}

# ---------------------------------------------------------------- relays
def _relay_url(raw: str) -> str:
    raw = raw.strip()
    if not raw:
        return ""
    return raw if "://" in raw else "wss://" + raw

def _relay_host(url: str) -> str:
    """wss://host[:443][/path] -> host (same-host variants collapse)."""
    h = url.split("://", 1)[-1].split("/", 1)[0].strip().lower()
    if h.endswith(":443"):
        h = h[:-4]
    return h

RELAY_CERT_SKIP_S = 3600           # distrust broken-certificate relays for
                                   # an hour (frontends rotate certs; keep
                                   # the skip short in case the cause was
                                   # transient/on our side)

def _relay_cert_bad() -> set:
    now = time.time()
    return {h for h, ts in (SETTINGS.get("relay_cert_fail") or {}).items()
            if isinstance(ts, (int, float)) and now - ts < RELAY_CERT_SKIP_S}

# ---- persistent settings (survive restarts, editable via /set) ----------
SETTINGS_FILE = APP_DIR / "settings.json"

def load_settings() -> dict:
    s = {"relays": [], "boost_relays": [], "proxy": "", "alert": True,
         "relay_cert_fail": {}}
    try:
        data = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        if isinstance(data, dict):
            for k in s:
                if k in data:
                    s[k] = data[k]
            if not isinstance(s.get("relay_cert_fail"), dict):
                s["relay_cert_fail"] = {}
    except Exception as e:
        _dbg(f"settings unreadable, using defaults: {e}")
    for key, cap in (("relays", 8), ("boost_relays", 5)):
        urls = []
        for u in (s.get(key) or [])[:cap]:
            nu = _relay_url(str(u))
            if nu and "://" in nu:
                urls.append(nu)
        s[key] = urls
    p = str(s.get("proxy") or "").strip()
    s["proxy"] = p if re.match(r"^(https?|socks[45h])://", p, re.I) else ""
    s["alert"] = bool(s.get("alert", True))
    return s

def save_settings():
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        SETTINGS_FILE.write_text(json.dumps(SETTINGS, indent=2) + "\n",
                                 encoding="utf-8")
    except Exception as e:
        sysline(f"(could not save settings: {e})")

SETTINGS = load_settings()

def _haversine(lat1, lon1, lat2, lon2) -> float:
    R = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))

def parse_relay_csv(text: str):
    relays = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.lower().startswith("relay url"):
            continue
        parts = line.split(",")
        if len(parts) < 3:
            continue
        url = _relay_url(parts[0])
        try:
            lat, lon = float(parts[1]), float(parts[2])
        except ValueError:
            continue
        if url:
            relays.append((url, lat, lon))
    return relays

def load_relay_csv(candidates):
    for path in candidates:
        try:
            relays = parse_relay_csv(path.read_text(encoding="utf-8"))
            if relays:
                return relays
        except Exception as e:
            _dbg(f"relay csv {path} unusable: {e}")
            continue
    return None

def refresh_relay_csv_quiet():
    """Refresh the relay CSV from the app's live source when stale."""
    cache = APP_DIR / "nostr_relays.csv"
    if cache.exists() and (time.time() - cache.stat().st_mtime) < 86400:
        return
    try:
        import urllib.request
        req = urllib.request.Request(GEORELAYS_URL,
                                     headers={"User-Agent": "bitchat-cli"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = resp.read()
        parsed = parse_relay_csv(data.decode("utf-8", "replace"))
        if len(parsed) < 10:
            _dbg(f"relay csv refresh: only {len(parsed)} usable rows, "
                 "keeping cached file")
            return
        APP_DIR.mkdir(parents=True, exist_ok=True)
        tmp = cache.with_suffix(".csv.tmp")
        tmp.write_bytes(data)
        os.replace(tmp, cache)            # atomic: concurrent readers never
                                          # see a half-written csv
    except Exception as e:
        _dbg(f"relay csv refresh skipped: {e}")

def relays_closest_to(geohash: str, n: int = N_RELAYS):
    override = SETTINGS.get("relays") or []
    boost = SETTINGS.get("boost_relays") or []
    cert_bad = _relay_cert_bad()
    if override:
        urls, seen_hosts = [], set()
        for url in override:
            h = _relay_host(url)
            if h in seen_hosts:
                continue
            seen_hosts.add(h)
            urls.append(url)
    else:
        lat, lon = geohash_center(geohash)
        relays = load_relay_csv((APP_DIR / "nostr_relays.csv",
                                 Path(__file__).parent / "nostr_relays.csv"))
        if not relays:
            urls, seen_hosts = [], set()
            for url in APP_DEFAULT_RELAYS:
                h = _relay_host(url)
                if h in seen_hosts or h in cert_bad:
                    continue
                seen_hosts.add(h)
                urls.append(url)
        else:
            relays.sort(key=lambda r: _haversine(lat, lon, r[1], r[2]))
            urls, seen_hosts = [], set()
            for url, _lat, _lon in relays:
                h = _relay_host(url)
                if h in seen_hosts or h in cert_bad:
                    continue
                seen_hosts.add(h)
                urls.append(url)
                if len(urls) >= n:
                    break
    for url in boost:                       # extras go last: 5-nearest stay
        if url not in urls:
            urls.append(url)
    return urls

# ---------------------------------------------------------------- Node
class Node:
    """
    Maintains websockets to the nearest relays of the active geohash, subscribes
    kind 20000+20001 with #g filter, publishes and heartbeats presence.

    Callbacks (asyncio loop context):
      on_message(nick, pubkey, text, created_at)
      on_presence(pubkey, created_at)
      on_status(text)
      on_ack(event_id, ok: bool, message: str)
      on_dm(sender_pubkey, rumor_dict)      # kind 1059 envelope opened
    """

    def __init__(self, seed: bytes, nick: str = "", verbose: bool = False):
        self.seed = seed
        self.nick = nick[:MAX_NICK_LEN]
        self.verbose = verbose
        self.geohash = None
        self.relay_urls = []
        self.sub_id = "bitchat-cli"
        self.on_message = None
        self.on_presence = None
        self.on_status = None
        self.on_ack = None
        self.on_dm = None
        self.seen = deque(maxlen=4000)
        self.seen_set = set()
        self.nick_by_pub = {}
        self.participants = {}          # pub -> last_seen epoch
        self.relay_state = {}           # url -> str
        self._outq = {}                 # url -> deque[(ev, expire_mono)]
        self._gen = 0
        self._loop_gen = {}             # url -> generation the REQ was sent for
        self._url_to_task = {}
        self._presence_task = None
        self._geo_cache = {}            # geohash -> (priv_hex, pub_hex, npub)
        self._stop = False
        self.proxy = (str(SETTINGS.get("proxy") or "").strip()) or None
        self._sent = {}                 # eid -> event (for PoW re-mining)
        self._pow_parent = {}           # re-mined eid -> original eid
        self._pow_live: set = set()     # eids already being mined
        self._pow_tasks = []
        # incoming-event verification: the pure-python schnorr check takes
        # tens of ms, so live mode runs it in a worker pool and applies the
        # results in arrival order (backlog bursts must not stall the loop)
        self._loop = None                # running loop once start() ran
        self._sig_pool = None            # verify workers
        self._pending_sig = {}           # seq -> event awaiting verification
        self._vready = {}                # seq -> event(ok) / None(rejected)
        self._vseq_next = 0
        self._vseq_apply = 0
        self._last_created = {}          # url -> newest created_at seen

    # ---- per-geohash identity ----
    def _geo_identity(self, gh: str):
        hit = self._geo_cache.get(gh)
        if hit is None:
            priv_hex = derive_seed_priv(self.seed, gh).hex()
            pub_hex = secp.pubkey_xonly(bytes.fromhex(priv_hex))[0].hex()
            hit = (priv_hex, pub_hex, npub_encode(pub_hex))
            self._geo_cache[gh] = hit
        return hit

    def npub_for(self, gh: str | None = None) -> str:
        gh = gh or self.geohash
        return self._geo_identity(gh)[2] if gh else ""

    def pubkey_for(self, gh: str) -> str:
        return self._geo_identity(gh)[1]

    # ---- lifecycle ----
    async def start(self, geohash: str | None = None):
        self._stop = False
        self._loop = asyncio.get_running_loop()
        self._sig_pool = concurrent.futures.ThreadPoolExecutor(
            max_workers=4, thread_name_prefix="bitchat-verify")
        self._presence_task = asyncio.create_task(self._presence_loop())
        if geohash:
            await self.set_channel(geohash)

    async def stop(self):
        self._stop = True
        for t in list(self._url_to_task.values()):
            t.cancel()
        tasks = list(self._url_to_task.values())
        if self._presence_task:
            self._presence_task.cancel()
            tasks.append(self._presence_task)
        await asyncio.gather(*tasks, return_exceptions=True)
        self._url_to_task.clear()
        self._presence_task = None
        if self._sig_pool:
            self._sig_pool.shutdown(wait=False)
            self._sig_pool = None

    async def set_channel(self, geohash: str):
        geohash = geohash.strip().lower()
        geohash_bounds(geohash)                       # validates charset/length
        self._gen += 1
        self.geohash = geohash
        self.participants = {}
        new_urls = relays_closest_to(geohash)
        old_urls = set(self.relay_urls)
        self.relay_urls = new_urls
        sysline(f"joined channel #({geohash}) {geohash_level_name(geohash)}  |  "
                f"relays: {', '.join(u.replace('wss://', '') for u in new_urls)}")
        for url in new_urls:
            task = self._url_to_task.get(url)
            if task is None or task.done():
                self._url_to_task[url] = asyncio.create_task(self.relay_loop(url))
        for url in old_urls - set(new_urls):
            task = self._url_to_task.pop(url, None)
            if task:
                task.cancel()
        # immediate presence announcement in the new channel
        self.send_presence()

    # ---- publishing ----
    def publish(self, ev: dict, only: str | None = None):
        eid = ev.get("id")
        if eid:
            self._sent[eid] = ev
            if len(self._sent) > 128:
                self._sent.pop(next(iter(self._sent)))
        urls = [only] if only else self.relay_urls
        for url in urls:
            q = self._outq.setdefault(url, deque())
            if len(q) < 30:
                q.append((ev, time.monotonic() + 30))

    def send_message(self, text: str) -> dict | None:
        if not self.geohash:
            return None
        text = text[:MAX_TEXT_LEN]
        priv_hex, _pub, _npub = self._geo_identity(self.geohash)
        tags = [["g", self.geohash]]
        if self.nick:
            tags.append(["n", self.nick])
        ev = sign_event(priv_hex, KIND_MSG, tags, text)
        self.publish(ev)
        return ev

    def send_presence(self):
        if not self.geohash:
            return
        priv_hex, _pub, _npub = self._geo_identity(self.geohash)
        self.publish(sign_event(priv_hex, KIND_PRESENCE,
                                [["g", self.geohash]], ""))

    async def _presence_loop(self):
        try:
            while not self._stop:
                await asyncio.sleep(random.uniform(PRESENCE_MIN_S, PRESENCE_MAX_S))
                if self._stop or not self.geohash:
                    continue
                self.send_presence()
        except asyncio.CancelledError:
            pass

    # ---- relay loops ----
    async def relay_loop(self, url: str):
        attempt = 0
        first = True
        while not self._stop:
            try:
                async with websockets.connect(
                        url, open_timeout=10, close_timeout=3,
                        max_size=2 ** 21, ping_interval=20,
                        ping_timeout=10, proxy=self.proxy) as ws:
                    attempt = 0
                    self.relay_state[url] = "online"
                    self._status(f"relay {url} online")
                    if first:
                        await self._subscribe_on(ws)
                        first = False
                    else:
                        # a reconnect only replays what this relay holds for
                        # our gap - not a full hour of backlog again (small
                        # bursts after flaky-relay disconnects)
                        gap = max(self._last_created.get(url, 0) - 5,
                                  int(time.time()) - RECONNECT_BACKLOG_S)
                        await self._subscribe_on(ws, since_ts=gap)
                    q = deque(self._outq.get(url, deque()))
                    self._outq[url] = deque()
                    while q:
                        ev, exp = q.popleft()
                        if time.monotonic() < exp:
                            await ws.send(json.dumps(["EVENT", ev]))
                    while not self._stop:
                        try:
                            raw = await asyncio.wait_for(ws.recv(), timeout=0.3)
                            self._handle_relay_message(raw, url)
                        except asyncio.TimeoutError:
                            if self._gen != self._loop_gen.get(url, self._gen):
                                self._loop_gen[url] = self._gen
                                await self._subscribe_on(ws, backlog=10)
                            while self._outq.get(url):
                                ev, exp = self._outq[url].popleft()
                                if time.monotonic() < exp:
                                    await ws.send(json.dumps(["EVENT", ev]))
                self._loop_gen.pop(url, None)
            except asyncio.CancelledError:
                return
            except Exception as e:
                if "certificate verify failed" in str(e).lower() or \
                        "sslcert" in type(e).__name__.lower():
                    self._mark_cert_fail(url)
                if self.verbose:
                    self._status(f"relay {url} failed: "
                                 f"{type(e).__name__}: {e}")
            if self._stop:
                return
            attempt += 1
            # reconnects are cheap now (only a small gap replay), so probe
            # instead of waiting blind minutes between attempts
            delay = min(60.0, 2.0 ** min(attempt - 1, 6))
            self.relay_state[url] = f"retry in {delay:.0f}s"
            self._status(f"relay {url} down - retrying every ~{delay:.0f}s")
            try:
                await asyncio.sleep(delay)
            except asyncio.CancelledError:
                return

    def _mark_cert_fail(self, url: str):
        """Persist distrust for relays with broken TLS - keeps dead hosts
        out of future selections (self-healing after ~3 days)."""
        try:
            host = _relay_host(url)
            fails = SETTINGS.setdefault("relay_cert_fail", {})
            if fails.get(host) is None:
                fails[host] = time.time()
                save_settings()
                self._status(f"relay {host} has a broken certificate - "
                             "avoiding it for 1 hour")
        except Exception as e:
            _dbg(f"cert-fail persist failed: {e}")

    async def _subscribe_on(self, ws, backlog: int | None = None,
                            since_ts: int | None = None):
        gh = self.geohash
        if not gh:
            return
        since_val = (int(since_ts) if since_ts is not None
                     else int(time.time()) -
                     (backlog if backlog is not None else SUB_BACKLOG_SINCE))
        filt = {"kinds": [KIND_MSG, KIND_PRESENCE], "#g": [gh],
                "since": since_val, "limit": SUB_BACKLOG_LIMIT}
        try:
            await ws.send(json.dumps(["REQ", self.sub_id, filt]))
        except Exception as e:
            _dbg(f"REQ send failed: {e}")
        # DM gift wraps (kind 1059) addressed to this channel's identity
        try:
            dm_filt = {"kinds": [1059], "#p": [self.pubkey_for(gh)],
                       "since": int(time.time()) - SUB_BACKLOG_SINCE,
                       "limit": SUB_BACKLOG_LIMIT}
            await ws.send(json.dumps(["REQ", self.sub_id + "-dm", dm_filt]))
        except Exception as e:
            _dbg(f"dm REQ send failed: {e}")

    def _status(self, text):
        if self.verbose:
            sysline(text)
        elif self.on_status:
            self.on_status(text)

    def _on_dm_gift(self, ev: dict):
        eid = ev.get("id", "")
        if eid in self.seen_set:
            return
        gh = self.geohash
        if not gh:
            return
        self.seen_set.add(eid)
        self.seen.append(eid)
        want = str(tag_value(ev, "p") or "").lower()
        if want != self.pubkey_for(gh).lower():
            return                    # gift for a different geohash identity
        rumor = dm_open_gift(ev, self._geo_identity(gh)[0])
        if not rumor:
            if self.verbose:
                self._status(f"(dm {eid[:8]}: envelope sealed to this key but "
                             "did not open)")
            return
        if self.on_dm:
            self.on_dm(str(rumor.get("pubkey") or "").lower(), rumor)

    def _handle_relay_message(self, raw: str, url: str):
        try:
            m = json.loads(raw)
        except ValueError:
            return
        if not (isinstance(m, list) and m):
            return
        typ = m[0]
        if typ == "EVENT" and len(m) >= 3 and isinstance(m[2], dict):
            ev = m[2]
            try:
                ts = int(ev.get("created_at") or 0)
                if ts > self._last_created.get(url, 0):
                    self._last_created[url] = ts    # reconnect-gap anchor
            except (TypeError, ValueError):
                pass                                # malformed created_at: the
                                                    # cheap prefilter rejects it
            self._on_event(ev)
        elif typ == "OK" and len(m) >= 3:
            eid, accepted = m[1], bool(m[2])
            msg = m[3] if len(m) > 3 else ""
            if not accepted and eid in self._sent and \
                    "pow" in (msg or "").lower() and eid not in self._pow_parent:
                dm = (re.search(r"pow\D*(\d{1,2})", msg, re.I)
                      or re.search(r"difficulty\D*(\d{1,2})", msg, re.I))
                if dm:
                    self._start_pow(url, eid, int(dm.group(1)))
            # an ack for a re-mined event counts for the original message
            if self.on_ack:
                self.on_ack(self._pow_parent.get(eid, eid), accepted, msg)
            if not accepted:
                self._status(f"{url.replace('wss://', '')} rejected {eid[:8]}: {msg}")

    def _start_pow(self, url: str, eid: str, difficulty: int):
        """Relay demands NIP-13 PoW: mine in a thread, resend to that relay."""
        ev = self._sent.get(eid)
        if not ev or eid in self._pow_live or eid in self._pow_parent:
            return
        if not (8 <= difficulty <= 24):
            self._status(f"pow difficulty {difficulty} not feasible - "
                         "no retry")
            return
        gh = self.geohash                      # identity is per-geohash
        self._pow_live.add(eid)
        self._status(f"{url.replace('wss://', '')} wants proof-of-work "
                     f"{difficulty} - mining, will resend...")
        async def _go():
            try:
                if not self.geohash or self.geohash != gh:
                    return                     # channel changed meanwhile
                priv_hex, _pu, _np = self._geo_identity(gh)
                mined = await asyncio.to_thread(nip13_mine, priv_hex,
                                                ev, difficulty)
                if not mined:
                    return
                self._pow_parent[mined["id"]] = eid
                self._status(f"pow {difficulty} mined "
                             f"{mined['id'][:8]} -> {url.replace('wss://', '')}")
                self.publish(mined, only=url)
            except Exception as e:
                self._status(f"pow mining failed: "
                             f"{type(e).__name__}: {e}")
            finally:
                self._pow_live.discard(eid)
        task = asyncio.create_task(_go())
        self._pow_tasks.append(task)

    def _on_event(self, ev: dict):
        if self.geohash is None:
            return
        if int(ev.get("kind", 0)) == 1059:          # DM gift wrap envelope
            self._on_dm_gift(ev)
            return
        eid = str(ev.get("id") or "")
        if eid in self.seen_set:                    # dedupe BEFORE verify:
            return                                  # the 4 duplicate copies
        if not self._cheap_ok(ev, eid):             # from other relays must
            return                                  # not each pay ~30ms work
        self.seen_set.add(eid)
        self.seen.append(eid)
        if self._loop is None or self._sig_pool is None:   # offline/test scripts
            if not verify_event(ev, self.geohash):
                return
            self._apply_event(ev)
            return
        # the schnorr check is tens of ms of pure-python point math: run it
        # in workers so a backlog burst never stalls live delivery, then
        # apply the results strictly in arrival order
        seq = self._vseq_next
        self._vseq_next += 1
        self._pending_sig[seq] = ev
        fut = self._loop.run_in_executor(self._sig_pool, verify_event,
                                         ev, self.geohash)
        fut.add_done_callback(lambda f, s=seq: self._sig_checked(s, f))

    def _cheap_ok(self, ev: dict, eid: str) -> bool:
        """Fast inline rejection of junk: shape, kind, channel, freshness
        and the (cheap, sha256-based) event-id binding of the content.
        The signature itself stays the job of verify_event()."""
        try:
            kind = int(ev.get("kind", 0))
            if kind not in (KIND_MSG, KIND_PRESENCE):
                return False
            pub = str(ev.get("pubkey") or "").lower()
            if len(pub) != 64 or len(eid) != 64:
                return False
            ts = int(ev.get("created_at") or 0)
            now = time.time()
            if ts < now - 2 * SUB_BACKLOG_SINCE or ts > now + FUTURE_SLACK_S:
                return False
            if tag_value(ev, "g") != self.geohash.lower():
                return False
            return event_id(pub, ts, kind, ev.get("tags"),
                            ev.get("content")).hex() == eid
        except Exception:
            return False

    def _sig_checked(self, seq: int, fut):
        ok = False
        try:
            ok = bool(fut.result())
        except Exception as e:
            _dbg(f"signature check crashed: {e}")
        self._vready[seq] = self._pending_sig.pop(seq, None) if ok else None
        while self._vseq_apply in self._vready:
            ev = self._vready.pop(self._vseq_apply)
            self._vseq_apply += 1
            if ev is None or self._stop:
                continue
            try:
                self._apply_event(ev)
            except Exception as e:
                self._status(f"event dispatch failed: "
                             f"{type(e).__name__}: {e}")

    def _apply_event(self, ev: dict):
        # the channel may have changed while a verification was in flight
        if self.geohash is None or \
                tag_value(ev, "g") != self.geohash.lower():
            return
        pub = ev["pubkey"].lower()
        kind = ev["kind"]
        nick = tag_value(ev, "n")
        if nick:
            self.nick_by_pub[pub] = str(nick)[:MAX_NICK_LEN]
        self.participants[pub] = int(ev.get("created_at", 0)) or int(time.time())
        try:
            own = pub == self.pubkey_for(self.geohash)
        except Exception as e:
            _dbg(f"own-pubkey check failed: {e}")
            own = False
        if own:
            return
        if kind == KIND_PRESENCE:
            if self.on_presence:
                self.on_presence(pub, int(ev.get("created_at", 0)))
            return
        content = ev.get("content") or ""
        if not content.strip():
            return                       # teleport marker / empty ephemeral
        if self.on_message:
            self.on_message(self.display_name(pub), pub,
                            int(ev.get("created_at", 0)), content)

    def display_name(self, pub: str) -> str:
        return self.nick_by_pub.get(pub, "anon")

    def alive_pubs(self) -> dict:
        cutoff = time.time() - PARTICIPANT_TTL_S
        for pub in list(self.participants):
            if self.participants[pub] < cutoff:
                del self.participants[pub]
        return dict(self.participants)

# ---------------------------------------------------------------- UI
# readable on light & dark terminals, plain 16-color ANSI for compatibility
USER_PALETTE = ["36", "32", "33", "35", "94", "96", "92", "93",
                "95", "34", "91", "37"]   # 12 distinct colors

HELP = """commands:
  /geo <lat,lon> [level]    join location channel by coordinates
                            level: region(2) province(4) city(5)
                            neighborhood(6) block(7, default) building(8)
  /geo <geohash>            join by geohash directly (2-8 base32 chars)
  /geo                      show current channel
  /who                      who is here (last 5 min)
  /relays                   relay connection status
  /npub                     your per-channel npub (this changes per channel!)
  /nick <name>              set nickname (max 15 chars)
  /msg                      explain DM handling (sender-only visibility)
  /alert on|off             bell + bold when someone mentions your nick
  /set                      relay override / boost / proxy (settings.json)
  /history [N]              last N messages this session (default 20)
  /last <nick>              recent messages from one person this session
  /find <text>              search this session in the current channel
  /clear                    clear screen
  /q                        quit

Your own messages show in the chat too, with your nick. The dot after them:
  ● yellow = sending (no relay has confirmed yet)
  ● green  = sent (at least one relay accepted it)

Plain text goes to the current channel. Tips:
  * Exactly like on phones: you chat with whoever is ON the same geochannel
    at the same time. Silence = nobody around; region channels (2 chars) are
    the widest / liveliest."""

class UI:
    def __init__(self, node: Node, ident: Identity):
        self.node = node
        self.ident = ident
        self.queue: asyncio.Queue | None = None
        self._acked = {}
        self._ack_total = {}
        self._user_colors: dict[str, str] = {}   # pub -> palette color code
        self._last_pub: str | None = None        # current message-group author
        self._last_ts: float = 0.0
        self._pending: dict[str, dict] = {}      # eid -> dot state (own msgs)
        self.tui = None                          # TuiChat when --tui is on
        self.alert = bool(SETTINGS.get("alert", True))   # bell+bold on mentions
        self.ring: deque = deque(maxlen=2000)    # session history per channel
        self._announced: set = set()             # pubs greeted in channel
        self._nick_seen: dict = {}               # pub -> last announced nick
        self._room_gh: str | None = None         # channel we announce for
        self._settled_until: float = 0.0         # no join spam during backlog
        self._logf = None                        # open channel log file
        self._log_gh: str | None = None
        self._log_ok = True

    async def run(self, geohash: str | None, tui: bool = False):
        node = self.node
        node.on_message = self.show_message
        node.on_presence = self.show_presence
        node.on_ack = self.on_ack
        node.on_status = self.show_status
        node.on_dm = self.show_dm
        loop = asyncio.get_running_loop()
        self.queue = asyncio.Queue()
        if tui:
            if sys.stdout.isatty():
                self.tui = TuiChat(self)
                self.tui.enter()
                global log, sysline
                log = self.tui.log_line           # everything lands in the pane
                sysline = self.tui.log_event
                threading.Thread(target=self.tui._input_loop, args=(loop,),
                                 daemon=True).start()
                self.tui._task = asyncio.create_task(self.tui._renderer())
            else:
                log(red("--tui needs a real terminal - using scroll log"))
        if self.tui is None:
            threading.Thread(target=self.input_thread, args=(loop,),
                             daemon=True).start()
        self._room_task = asyncio.create_task(self._room_loop())

        log(bold("bitchat") + dim("  |  CLI <-> official app internet mode "
                                  "(geochat over Nostr)"))
        if geohash:
            try:
                await node.set_channel(geohash)
                self.ident.save(geohash)
            except Exception as e:
                log(red(f"bad channel '{geohash}': {e}"))
                geohash = None
        if not node.geohash:
            log(yellow("not in a channel yet - join with /geo <lat,lon> or "
                       "/geo <geohash>  (like choosing a location channel in "
                       "the phone app)"))
        log(dim("/help for commands\n"))

        try:
            while True:
                line = await self.queue.get()
                line = line.rstrip("\r")
                if line.startswith("/"):
                    await self.command(line)
                else:
                    self.send_text(line)
        except KeyboardInterrupt:
            log(dim("bye"))
        except asyncio.CancelledError:
            log(dim("bye"))
        finally:
            self._close_log()
            if self.tui is not None:
                self.tui.close()

    def input_thread(self, loop):
        try:
            while True:
                line = input()
                loop.call_soon_threadsafe(self.queue.put_nowait, line)
        except EOFError:
            while True:
                time.sleep(1)
        except Exception:
            loop.call_soon_threadsafe(self.queue.put_nowait, "/q")

    async def command(self, raw: str):
        parts = raw.strip().split()
        cmd = parts[0].lower()
        args = parts[1:]
        node = self.node

        if cmd in ("/q", "/quit", "/exit"):
            raise KeyboardInterrupt
        elif cmd == "/help":
            log(HELP)
        elif cmd == "/clear":
            if self.tui is not None:
                del self.tui.entries[:]
                self.tui.dirty = True
            else:
                print("\x1b[2J\x1b[H", end="", flush=True)
                _cursor_rows[0] = 0              # screen is fresh, counter too
        elif cmd in ("/geo", "/go"):
            await self.cmd_geo(args)
        elif cmd == "/who":
            self.cmd_who()
        elif cmd == "/relays":
            self.cmd_relays()
        elif cmd == "/npub":
            npub = node.npub_for()
            if npub:
                log(f"your npub in this channel: {bold(npub)}")
                log(dim("(one key per geohash, derived from your seed exactly "
                        "like the app does: channels unlink your pseudonyms)"))
            else:
                log(dim("not in a channel"))
        elif cmd == "/nick":
            if args:
                nick = " ".join(args).strip()[:MAX_NICK_LEN]
                if nick:
                    self.ident.nick = node.nick = nick
                    self.ident.save(node.geohash)
                    log(dim(f"nickname set: {nick}"))
            else:
                log(f"nickname: {node.nick}   (usage: /nick name)")
        elif cmd == "/msg":
            log(yellow("DMs do reach this CLI: they arrive as NIP-17 gift "
                       "wraps and the [dm] line shows who/when. But phone "
                       "bodies are mesh-Noise encrypted (sessions born over "
                       "BLE), so the text is readable on your phone only."))
            npub = node.npub_for()
            if npub:
                log(dim(f"your current npub (share on the phone to DM via "
                        f"favorites): {npub}"))
        elif cmd == "/alert":
            word = args[0].lower() if args else ("on" if self.alert else "off")
            if word not in ("on", "off"):
                log(dim("usage: /alert on|off"))
            else:
                self.alert = word == "on"
                SETTINGS["alert"] = self.alert
                save_settings()
                log(dim(f"mention alerts {'on' if self.alert else 'off'} "
                        "(saved)"))
        elif cmd == "/set":
            self.cmd_set(args)
        elif cmd == "/history":
            self.cmd_history(args)
        elif cmd == "/last" and args:
            self.cmd_last(" ".join(args))
        elif cmd == "/find" and args:
            self.cmd_find(" ".join(args))
        elif cmd == "/bye":
            raise KeyboardInterrupt
        else:
            log(dim(f"unknown command '{cmd}' - /help"))

    async def cmd_geo(self, args):
        node = self.node
        if not args:
            if node.geohash:
                log(f"current channel: {bold('#' + node.geohash)} "
                    f"({geohash_level_name(node.geohash)})")
            else:
                log(dim("usage: /geo <lat,lon> [level] | /geo <geohash>"))
            return
        target = args[0]
        level = 7
        if len(args) >= 2:
            lvl = args[1].lower()
            matched = False
            for prec, name in ((2, "region"), (4, "province"), (5, "city"),
                               (6, "neighborhood"), (7, "block"), (8, "building")):
                if lvl == name or lvl == str(prec) or (name.startswith(lvl) and lvl):
                    level = prec
                    matched = True
                    break
            if not matched:
                log(red(f"unknown level '{args[1]}' - use region/province/city/"
                        "neighborhood/block/building"))
                return
        if "," in target:
            try:
                lat, lon = [float(x) for x in target.split(",")[:2]]
            except ValueError:
                log(red("bad coordinates - example: /geo 43.6532,-79.3832"))
                return
            await self.switch(geohash_encode(lat, lon, level))
        else:
            gh = target.lower()
            if any(ch not in _B32 for ch in gh) or not (2 <= len(gh) <= 8):
                log(red("bad geohash (2-8 base32 chars: 0-9 a-z minus i,l,o)"))
                return
            await self.switch(gh)

    async def switch(self, gh: str):
        node = self.node
        node.geohash = None
        try:
            await node.set_channel(gh)
            self.ident.save(gh)
        except Exception as e:
            log(red(f"could not switch: {e}"))

    def cmd_who(self):
        node = self.node
        alive = node.alive_pubs()
        if not node.geohash:
            log(dim("no channel joined"))
            return
        log(f"people in #{node.geohash}: {len(alive)} "
            f"(last {PARTICIPANT_TTL_S // 60} min)")
        try:
            me = node.pubkey_for(node.geohash).lower()
        except Exception:
            me = ""
        for pub, ts in sorted(alive.items(), key=lambda kv: -kv[1]):
            who = node.display_name(pub)
            if who == "anon":
                who = f"anon({pub[:6]})"
            mins = max(0, int(time.time() - ts) // 60)
            suffix = "  (you)" if pub == me else ""
            log(f"   {who}{suffix}: last seen {mins} min ago")

    def cmd_relays(self):
        node = self.node
        if not node.relay_urls:
            log(dim("no relays - not in a channel"))
            return
        log(f"nearest relays to #{node.geohash or ''}:")
        for url in node.relay_urls:
            log(f"   {url.replace('wss://', ''):38} {node.relay_state.get(url, 'connecting')}")

    def cmd_history(self, args):
        try:
            n = int(args[0]) if args else 20
        except ValueError:
            n = 20
        n = max(1, min(n, 200))
        gh = self.node.geohash
        msgs = [e for e in self.ring if e[1] == gh]
        if not msgs:
            log(dim("nothing in this channel this session yet"))
            return
        log(bold(f"session history in #{gh}: last {min(n, len(msgs))} of "
                 f"{len(msgs)}"))
        for ts, _gh, nick, pub, text, _own in msgs[max(0, len(msgs) - n):]:
            t = time.strftime("%H:%M", time.localtime(ts))
            log(f"  {dim(t)} {_c(f'{self.user_color(pub)};1', nick)} {text}")

    def cmd_last(self, who: str):
        who = who.lower()
        gh = self.node.geohash
        msgs = [e for e in self.ring
                if e[1] == gh and e[2] and e[2].lower().startswith(who)]
        if not msgs:
            log(dim(f"nothing from '{who}' this session"))
            return
        log(bold(f"last {min(10, len(msgs))} of {len(msgs)} from "
                 f"'{msgs[-1][2]}':"))
        for ts, _gh, nick, pub, text, _own in msgs[-10:]:
            t = time.strftime("%H:%M", time.localtime(ts))
            log(f"  {dim(t)} {_c(f'{self.user_color(pub)};1', nick)} {text}")

    def cmd_find(self, needle: str):
        gh = self.node.geohash
        low = needle.lower()
        hits = [e for e in self.ring if e[1] == gh and low in e[4].lower()]
        if not hits:
            log(dim(f"no match for '{needle}' this session"))
            return
        show = hits[-15:]
        log(bold(f"{len(hits)} match(es), newest last:"))
        for ts, _gh, nick, pub, text, _own in show:
            t = time.strftime("%H:%M", time.localtime(ts))
            log(f"  {dim(t)} {_c(f'{self.user_color(pub)};1', nick)} {text}")

    def cmd_set(self, args):
        node = self.node
        if not args:
            log(f"relays override: {bold(', '.join(SETTINGS['relays'])
                                            or 'none - auto 5 nearest')}")
            log(f"boost relays:     {', '.join(SETTINGS['boost_relays'])
                                            or 'none'}")
            log(f"proxy:            {bold(SETTINGS['proxy'] or 'none (direct)')}")
            log(dim("usage: /set relays <url1,url2|off>  pin relay set"))
            log(dim("       /set boost <url1,url2|off>  also publish via extra"))
            log(dim("       /set proxy <url|off>       http:// or socks5:// (Tor)"))
            log(dim("relay/proxy changes apply on /geo (re)join or restart"))
            return
        key = args[0].lower()
        if key in ("relays", "boost") and len(args) >= 2:
            field = "boost_relays" if key == "boost" else "relays"
            val = " ".join(args[1:])
            if val.lower() in ("off", "none", "auto", "default"):
                SETTINGS[field] = []
            else:
                urls = [u for u in (_relay_url(x)
                                    for x in val.replace(" ", "").split(","))
                        if u]
                SETTINGS[field] = urls
                log(f"saving {field}: {urls}")
            save_settings()
            label = "relay override" if field == "relays" else "boost relays"
            extra = ("switch channels (/geo) or restart to apply"
                     if node.geohash else "")
            log(green(f"{label} saved: "
                      f"{SETTINGS[field] or '(use default)'}"))
            if extra:
                log(dim(extra))
        elif key == "proxy" and len(args) >= 2:
            val = "" if args[1].lower() in ("off", "none") else args[1]
            if val and not re.match(r"^(https?|socks[45h])://", val, re.I):
                log(red("proxy must look like http://host:port or "
                        "socks5://host:port (e.g. Tor socks5://127.0.0.1:9050)"))
                return
            SETTINGS["proxy"] = val
            save_settings()
            node.proxy = val or None
            log(green(f"proxy saved: {val or 'none (direct)'}"))
            log(dim("rejoin (/geo) or restart to reconnect through it"))
        else:
            log(dim("usage: /set | /set relays <urls|off> | "
                    "/set boost <urls|off> | /set proxy <url|off>"))

    def show_presence(self, pub, created_at):
        pass                     # join/leave lines come from _room_loop

    # ---- room liveliness (join / leave / nick changes) ------------------
    async def _room_loop(self):
        try:
            while True:
                await asyncio.sleep(20)
                gh = self.node.geohash
                if gh != self._room_gh:
                    # (re)joined: greet nobody yet, skip the backlog burst
                    self._room_gh = gh
                    self._announced = set()
                    self._settled_until = time.time() + 35
                    continue
                now = time.time()
                if now < self._settled_until or not gh:
                    continue
                try:
                    me = self.node.pubkey_for(gh).lower()
                except Exception:
                    me = ""
                for pub in list(self.node.participants):
                    if pub == me:
                        continue              # never announce ourselves
                    if pub not in self._announced:
                        self._announce_join(pub)
                for pub in list(self._announced):
                    if pub == me:
                        continue
                    ts = self.node.participants.get(pub)
                    if ts is None or now - ts > PARTICIPANT_TTL_S:
                        self._announce_leave(pub)
        except asyncio.CancelledError:
            pass

    def _announce_join(self, pub: str):
        who = self._nick_seen.get(pub) or f"anon({pub[:4]})"
        self._announced.add(pub)
        sysline(f"{who} joined")

    def _announce_leave(self, pub: str):
        if pub in self._announced:
            self._announced.discard(pub)
            who = self._nick_seen.get(pub) or f"anon({pub[:4]})"
            sysline(f"{who} left")

    def _track_room(self, pub, nick):
        key = (pub or "").hex()[:16] if isinstance(pub, bytes) else str(pub)[:16]
        if key in self._announced:
            prev = self._nick_seen.get(key)
            if nick and prev and prev != nick:
                sysline(f"{prev} is now known as {nick}")
        if nick:
            self._nick_seen[key] = nick
        if key not in self._announced and \
                time.time() >= self._settled_until:
            self._announce_join(key)

    # ---- alerts ---------------------------------------------------------
    @staticmethod
    def _bell():
        try:
            sys.stdout.write("\a")
            sys.stdout.flush()
        except (OSError, ValueError, UnicodeEncodeError):
            pass                            # terminal bells are best-effort

    def _mentions_me(self, text: str) -> bool:
        nick = self.node.nick
        if not nick:
            return False
        return re.search(rf"(?<!\w){re.escape(nick)}(?!\w)", text,
                         re.IGNORECASE) is not None

    def _bold_nick(self, line: str) -> str:
        nick = self.node.nick
        return re.sub(rf"(?<!\w){re.escape(nick)}(?!\w)",
                      lambda m: bold(m.group(0)), line, flags=re.IGNORECASE)

    # ---- channel log / ring buffer --------------------------------------
    def _archive(self, ts: float, nick: str, pub, text: str, own: bool):
        gh = self.node.geohash
        self.ring.append((ts, gh, nick, pub, text, own))
        if not self._log_ok or not gh:
            return
        if gh != self._log_gh:
            self._close_log()
            try:
                d = APP_DIR / "logs"
                d.mkdir(parents=True, exist_ok=True)
                self._logf = open(d / f"{gh}.log", "a",
                                  encoding="utf-8", errors="replace")
                self._log_gh = gh
            except Exception as e:
                _dbg(f"channel log file unavailable ({gh}): {e}")
                self._log_ok = False                  # tolerate no-disk cases
                return
        try:
            stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(ts))
            who = "you" if own else nick
            body = text.replace("\r", " ").replace("\n", " ⏎ ")
            self._logf.write(f"{stamp} {who:<15} {body}\n")
            self._logf.flush()
        except Exception as e:
            _dbg(f"channel log write failed: {e}")
            self._log_ok = False

    def _close_log(self):
        if self._logf:
            try:
                self._logf.close()
            except OSError:
                pass              # nothing to do: log is being torn down anyway
        self._logf = None
        self._log_gh = None

    def show_dm(self, sender_pub: str, rumor: dict):
        """Phone DM arrived as a NIP-17 gift wrap; body is mesh-Noise
        encrypted, so we show who/when/what kind - not the text."""
        who = self.node.nick_by_pub.get(sender_pub)
        who = who or f"anon({sender_pub[:4]})"
        ts = int(rumor.get("created_at", 0)) or time.time()
        t = time.strftime("%H:%M", time.localtime(ts))
        color = self.user_color(sender_pub)
        npub = npub_encode(sender_pub)
        log(f"{dim(t)} {_c('35;1', '[dm]')} "
            f"{_c(f'{color};1', who)} sent you an end-to-end encrypted "
            f"message  ({npub[:16]}…)")
        pk = parse_bitchat_packet(str(rumor.get("content", "")))
        if pk:
            log(dim(f"         encrypted {pk['type_name']} packet, "
                    f"{pk['payload_len']} bytes, mesh peer "
                    f"{pk['sender_id'][:8]}"))
        log(dim("         the app encrypts DM bodies in its mesh-Noise "
                "session, so read this one on your phone - the CLI opens "
                "only the envelope"))

    def show_status(self, text):
        if self.tui is not None:
            self.tui.note(text)
            return
        if "rejected" in text or "failed" in text:
            sysline(text)

    def user_color(self, pub) -> str:
        key = (pub or "").hex()[:16] if isinstance(pub, bytes) else str(pub)[:16]
        if key not in self._user_colors:
            self._user_colors[key] = USER_PALETTE[
                len(self._user_colors) % len(USER_PALETTE)]
        return self._user_colors[key]

    def show_message(self, nick, pub, created_at, text, eid=None):
        ts = created_at or time.time()
        if self.tui is not None:              # alt-screen: feed the renderer
            self._archive(ts, nick, pub, text, own=eid is not None)
            if eid is None:
                self._track_room(pub, nick)
            self.tui.add_message(nick, pub, ts, text,
                                 own=eid is not None, eid=eid)
            return
        t = time.strftime("%H:%M", time.localtime(ts))
        color = self.user_color(pub)
        lines = text.splitlines() or [""]
        # group: suppress "HH:MM nick" header when the same person keeps
        # sending rapid consecutive messages (bots, fast typing)
        gap = ts - (self._last_ts or 0)
        show_header = (pub != self._last_pub) or gap > 120
        self._last_pub, self._last_ts = pub, ts
        # mention alert: bold your nick inside the text (skip own messages)
        if eid is None and self.alert and self._mentions_me(text):
            lines = [self._bold_nick(x) for x in lines]
        indent = " " * 22                       # len("HH:MM ") + nick column
        last = len(lines) - 1
        for i, line in enumerate(lines):
            if i == 0 and show_header:
                s = f"{dim(t)} {_c(f'{color};1', f'{nick:<15}')} {line}"
            else:
                s = indent + line
            if eid is not None and i == last:
                # our own message: remember the line, paint the status dot
                # right after printing it: ● yellow = sending, ● green = sent
                log(s)
                self._pending[eid] = {"pre": s,
                                      "n0": _cursor_rows[0]}
                self._repaint_dot(s, self._pending[eid]["n0"], "33")
            else:
                log(s)
        self._archive(ts, nick, pub, text, own=eid is not None)
        if eid is None and self.alert and self._mentions_me(text):
            self._bell()
        if eid is None:
            self._track_room(pub, nick)

    def _confirm(self, eid: str):
        """First relay OK: turn our message's dot yellow -> green."""
        if self.tui is not None:
            # TUI mode: the dot state lives in the pane entry (the scroll-
            # log _pending dict is never populated there)
            self.tui.ack(eid)
            return
        p = self._pending.pop(eid, None)
        if not p:
            return
        if not sys.stdout.isatty():
            return
        try:
            self._repaint_dot(p["pre"], p["n0"], "32")
        except Exception as e:
            _dbg(f"dot repaint failed: {e}")

    @staticmethod
    def _repaint_dot(pre: str, n0: int, color: str):
        """Cursor back to the pending dot row and repaint it (color code)."""
        if not sys.stdout.isatty():
            return
        k = _cursor_rows[0] - n0                # rows printed since the dot
        if k < 0:
            return
        vis = _plain(pre) + " ●"                # dot sits one space after text
        if "\n" in vis:
            return
        cols = _term_cols()
        length = _vis_len(vis)
        nrows = max(1, -(-length // cols))      # rows the message occupies
        tail = length - (nrows - 1) * cols      # visible chars on the dot row
        # wrapped lines: repaint the plain text tail (it only holds message
        # body; colored "HH:MM nick" sits 22 columns in) - bail if it would
        # reach into those colored parts
        if nrows > 1 and _ANSI_RE.search(pre) and length - tail < 22:
            return
        out = [f"\x1b[{k}A\r"]
        if nrows == 1:
            out.append(pre + " " + _c(color, "●") + "\x1b[K")
        else:
            out.append("\x1b[2K" + vis[-tail:][:-1] + _c(color, "●"))
        out.append(f"\x1b[{k}B\r")
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    def on_ack(self, eid, ok, msg):
        if not ok:
            return
        if eid in self._acked:               # chat messages only, not presence
            self._acked[eid] += 1
            if self._acked[eid] == 1:
                self._confirm(eid)           # dot yellow -> green, no sysline
            if len(self._acked) > 64:
                self._acked.pop(next(iter(self._acked)))
        # rejects surface via on_status / verbose lines

    def send_text(self, text: str):
        text = text.strip()
        if not text:
            return
        if not self.node.geohash:
            log(yellow("join a channel first: /geo <lat,lon> or /geo <geohash>"))
            return
        try:
            ev = self.node.send_message(text)
            if ev:
                self._acked[ev["id"]] = 0
                if len(self._pending) > 64:
                    self._pending.pop(next(iter(self._pending)))
                # show our own message with our nick, like we show others
                self.show_message(self.node.nick, ev["pubkey"],
                                  ev["created_at"], ev["content"],
                                  eid=ev["id"])
        except Exception as e:
            log(red(f"send failed: {e}"))

# ---------------------------------------------------------------- tests
RESULTS: list = []

def _assert(name, cond):
    RESULTS.append(bool(cond))
    log(("  PASS " if cond else "  FAIL ") + name)

def offline_tests() -> list:
    for lat, lon, prec in [(43.6532, -79.3832, 7), (40.7128, -74.0060, 5),
                           (51.5007, -0.1246, 8), (-33.8678, 151.2073, 4),
                           (35.6764, 139.65, 2), (59.9139, 10.7522, 6)]:
        gh = geohash_encode(lat, lon, prec)
        ok = len(gh) == prec and all(ch in _B32 for ch in gh)
        lat0, lat1, lon0, lon1 = geohash_bounds(gh)
        clat, clon = geohash_center(gh)
        ok = ok and lat0 <= lat <= lat1 and lon0 <= lon <= lon1
        ok = ok and lat0 <= clat <= lat1 and lon0 <= clon <= lon1
        _assert(f"geohash {lat:g},{lon:g}@{prec} -> {gh}", ok)

    seed = secrets.token_bytes(32)
    priv = derive_seed_priv(seed, "dr5rs")
    _assert("HMAC identity deterministic",
            priv == derive_seed_priv(seed, "dr5rs"))
    _assert("different geohash -> different pseudonym",
            derive_seed_priv(seed, "dr5rs") != derive_seed_priv(seed, "u4pru"))
    _assert("fallback derivation valid",
            0 < int.from_bytes(hashlash(seed, b"dr5rs"), "big") < secp.N)
    _assert("identity inside curve order",
            0 < int.from_bytes(priv, "big") < secp.N)
    _assert("pubkey derivable", len(priv_to_pub_hex(priv)) == 64)

    ev = sign_event(priv.hex(), KIND_MSG, [["g", "dr5rs"], ["n", "t"]], "hi")
    _assert("event verifies (id + sig + channel)", verify_event(ev, "dr5rs"))
    _assert("event verifies w/o channel filter", verify_event(ev, None))
    bad = dict(ev); bad["content"] = "h1"
    _assert("tampered content rejected", not verify_event(bad, "dr5rs"))
    bad = dict(ev); bad["tags"] = {"not": "list"}
    _assert("malformed tags rejected", not verify_event(bad, "dr5rs"))
    foreign = sign_event(priv.hex(), KIND_MSG, [["g", "uu2as"], ["n", "t"]], "hi")
    _assert("other-channel message rejected by client filter",
            not verify_event(foreign, "dr5rs"))

    np1 = npub_encode(priv_to_pub_hex(priv))
    _assert("npub encodes", np1.startswith("npub1") and len(np1) > 40)
    _assert("npub decodes to same key", npub_decode(np1) == priv_to_pub_hex(priv))
    try:
        npub_decode("npub1xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxbad")
        _assert("bad npub rejected", False)
    except Exception:
        _assert("bad npub rejected", True)

    urls = relays_closest_to("dr5rs", N_RELAYS)
    _assert("relay selection returns entries", len(urls) >= 3)
    _assert("relay urls normalized",
            all(u.startswith("wss://") for u in urls))

    p = secrets.token_bytes(32)
    ev = sign_event(p.hex(), KIND_MSG, [["g", "dr5rs"], ["n", "t"]], "pow me")
    mined = nip13_mine(p.hex(), ev, 8)
    _assert("nip13 mines difficulty 8",
            bool(mined) and pow_bits(mined["id"]) >= 8)
    _assert("mined event still verifies",
            bool(mined) and verify_event(mined, "dr5rs"))
    return RESULTS

def priv_to_pub_hex(priv: bytes) -> str:
    return secp.pubkey_xonly(priv)[0].hex()

async def selftest_live() -> list:
    """Two ephemeral identities exchange presence + message exactly like
    phones would, through the app's relay-selection logic. Retries with
    another random channel if the nearest relays are dead (listing quality
    varies) instead of failing the whole run."""
    log("\nlive test (needs internet)...")

    def recmsg(container, nick, pub, created, text):
        if text.startswith("ping from A"):
            container.append((nick, text))

    for attempt in range(3):
        gh = geohash_encode(random.uniform(-25, 55), random.uniform(-95, 95), 7)
        a_seed, b_seed = secrets.token_bytes(32), secrets.token_bytes(32)
        got = []
        na = Node(a_seed, "test-a")
        nb = Node(b_seed, "test-b")
        nb.on_message = lambda *a, _c=got: recmsg(_c, *a)
        try:
            await na.start(gh)
            await nb.start(gh)
            await asyncio.sleep(12.0)   # relays across the world vary in speed
            alive = sum(1 for s in na.relay_state.values() if s == "online")
            log(f"   relays online for #{gh}: {alive}/{len(na.relay_urls)}")
            if alive < 1:
                if attempt < 2:
                    log("   no relay came up for this channel - picking "
                        "another location")
                continue
            _assert("some relays connected", True)
            na.send_message("ping from A - selftest message")
            ok = False
            for _ in range(15):
                await asyncio.sleep(1.0)
                if got:
                    ok = True
                    break
            _assert("B received A's geochat message (official format)", ok)
            if got:
                log(f"        B saw: {got[0][0]}: {got[0][1][:50]}")
            await asyncio.sleep(2.0)
            a_pub = na.pubkey_for(gh).lower()
            _assert("B sees A's presence", a_pub in nb.alive_pubs())
            if not ok:
                for u, s in na.relay_state.items():
                    log(f"        {u} -> {s}")
            return RESULTS
        finally:
            await na.stop()
            await nb.stop()
    _assert("some relays connected", False)
    _assert("B received A's geochat message (official format)", False)
    _assert("B sees A's presence", False)
    return RESULTS

async def run_sniff(gh: str, seconds: float):
    gh = gh.strip().lower()
    urls = relays_closest_to(gh)
    log(f"sniffing #{gh} for {seconds:.0f}s on: "
        f"{', '.join(u.replace('wss://', '') for u in urls)}")
    filt = {"kinds": [KIND_MSG, KIND_PRESENCE], "#g": [gh],
            "since": int(time.time()) - SUB_BACKLOG_SINCE, "limit": 200}
    seen = set()

    async def one(url):
        try:
            async with websockets.connect(url, open_timeout=10) as ws:
                await ws.send(json.dumps(["REQ", "sniff", filt]))
                while True:
                    m = json.loads(await ws.recv())
                    if isinstance(m, list) and m[0] == "EVENT":
                        ev = m[2]
                        if ev.get("id") in seen:
                            continue
                        seen.add(ev.get("id"))
                        nick = tag_value(ev, "n") or "-"
                        content = (ev.get("content") or "")[:90]
                        t = time.strftime("%H:%M:%S",
                                          time.localtime(ev.get("created_at", 0)))
                        print(f"[{url.replace('wss://', ''):>26}] {t} k={ev['kind']}"
                              f" nick={nick:<12} pub={ev['pubkey'][:10]} {content!r}",
                              flush=True)
        except Exception as e:
            _dbg(f"sniff {url} lost: {e}")

    try:
        await asyncio.wait_for(asyncio.gather(*[one(u) for u in urls],
                                              return_exceptions=True),
                               timeout=seconds)
    except asyncio.TimeoutError:
        pass
    log(f"({len(seen)} unique events seen in {seconds:.0f}s)")

# ---------------------------------------------------------------- TUI
class TuiChat:
    """Alternate-screen UI (--tui): message pane + status bar + fixed input
    line. Windows-safe VT (Windows Terminal / conhost). The scroll log mode
    stays the default; this is opt-in per run."""

    def __init__(self, ui):
        self.ui = ui
        self.entries = []          # {'kind': msg|event|line, ...} play list
        self.scroll = 0            # rows back from the bottom; 0 = live
        self.buf = ""              # input line under construction
        self.note_text = ""        # transient status note (relay events)
        self.dirty = True
        self._task = None

    # ---- event entry points (asyncio loop context) ----------------------
    def add_message(self, nick, pub, ts, text, own, eid=None):
        self.entries.append({"kind": "msg", "nick": nick, "pub": pub,
                             "ts": ts, "text": text, "own": own, "eid": eid})
        if len(self.entries) > 4000:
            del self.entries[:1000]
        self.dirty = True
        if not own and self.ui.alert and self.ui._mentions_me(text):
            self.ui._bell()

    def log_line(self, line):            # re-bound module log() sink
        self.entries.append({"kind": "line", "text": line})
        if len(self.entries) > 4000:
            del self.entries[:1000]
        self.dirty = True

    def log_event(self, text):           # re-bound module sysline() sink
        self.entries.append({"kind": "event", "text": text})
        if len(self.entries) > 4000:
            del self.entries[:1000]
        self.dirty = True

    def note(self, text):
        self.note_text = text
        self.dirty = True

    def ack(self, eid):
        """Relay confirmed a pending own message: dot yellow -> green."""
        for e in reversed(self.entries):
            if e["kind"] == "msg" and e.get("eid") == eid:
                if not e.get("green"):
                    e["green"] = True
                    self.dirty = True
                break

    # ---- lifecycle -------------------------------------------------------
    def enter(self):
        try:
            sys.stdout.write("\x1b[?1049h\x1b[H\x1b[2J")
            sys.stdout.flush()
        except Exception as e:
            _dbg(f"tui enter failed: {e}")

    def close(self):
        if self._task:
            self._task.cancel()
            self._task = None
        try:
            sys.stdout.write("\x1b[0m\x1b[?1049l")
            sys.stdout.flush()
        except Exception as e:
            _dbg(f"tui close failed: {e}")

    # ---- renderer ---------------------------------------------------------
    async def _renderer(self):
        try:
            while True:
                await asyncio.sleep(0.15)
                if self.dirty:
                    self.dirty = False
                    try:
                        self.render()
                    except Exception as e:
                        _dbg(f"tui render failed: {e}")
        except asyncio.CancelledError:
            pass

    def _body_rows(self, cols):
        """Render entries into display rows (same grouping rules as the
        scroll-log mode)."""
        ui = self.ui
        rows = []
        last_pub, last_ts = None, 0.0
        indent = " " * 22
        for e in self.entries:
            if e["kind"] == "msg":
                ts = e["ts"]
                t = time.strftime("%H:%M", time.localtime(ts))
                color = ui.user_color(e["pub"])
                show_head = e["pub"] != last_pub or ts - last_ts > 120
                last_pub, last_ts = e["pub"], ts
                lines = e["text"].splitlines() or [""]
                if not e["own"] and ui.alert and ui._mentions_me(e["text"]):
                    lines = [ui._bold_nick(ln) for ln in lines]
                last = len(lines) - 1
                for i, ln in enumerate(lines):
                    if i == 0 and show_head:
                        base = f"{_c('90', t)} " \
                               f"{_c(f'{color};1', e['nick'][:15].ljust(15))} {ln}"
                    else:
                        base = indent + ln
                    if e.get("eid") is not None and i == last:
                        dot = "32" if e.get("green") else "33"
                        base += " " + _c(dot, "●")
                    rows.extend(_wrap_ansi(base, cols))
            elif e["kind"] == "event":
                rows.extend(_wrap_ansi(_c("90", e["text"]), cols))
            else:
                for piece in e["text"].split("\n"):
                    rows.extend(_wrap_ansi(piece, cols))
        return rows

    def _bar(self, cols):
        node = self.ui.node
        gh = getattr(node, "geohash", None) or "-"
        parts = [f"#{gh}"]
        rs = getattr(node, "relay_state", None)
        if isinstance(rs, dict) and rs:
            on = sum(1 for s in rs.values() if s == "online")
            parts.append(f"relays {on}/{len(rs)}")
        if self.scroll:
            parts.append(f"history +{self.scroll} rows")
        if self.note_text:
            used = sum(len(p) for p in parts) + 3 * len(parts)
            parts.append(self.note_text[: max(0, cols - used - 1)])
        s = " · ".join(parts)
        pad = max(0, cols - _vis_len(s))
        return _c("7", s + " " * pad)

    def render(self):
        cols, nrows = shutil.get_terminal_size((80, 24))
        cols = max(40, cols)
        nrows = max(14, nrows)
        msg_h = nrows - 2                     # bar + input take 2 rows
        body = self._body_rows(cols)
        self.scroll = max(0, min(self.scroll, max(0, len(body) - 1)))
        if self.scroll + msg_h > len(body):
            # full-page top view instead of a single pinned row
            self.scroll = max(0, len(body) - msg_h)
        end = len(body) - self.scroll
        start = max(0, end - msg_h)
        window = body[start:end]
        out = ["\x1b[H\x1b[2J"]
        for r in range(msg_h):
            if r < len(window):
                out.append("\x1b[2K" + window[r] + "\x1b[0m\r\n")
            else:
                out.append("\x1b[2K\r\n")
        out.append("\x1b[2K" + self._bar(cols) + "\r\n")
        out.append("\x1b[2K> " + self.buf + "\x1b[0m")
        sys.stdout.write("".join(out))
        sys.stdout.flush()

    # ---- input (Windows) --------------------------------------------------
    def _push(self, line):
        try:
            self.ui.queue.put_nowait(line)
        except Exception as e:
            _dbg(f"typed line dropped ({e})")

    def _input_loop(self, loop):
        import msvcrt
        while True:
            try:
                ch = msvcrt.getwch()
            except OSError:
                continue          # console released; unexpected errors here
                                  # should surface, not be swallowed
            if ch in ("\x00", "\xe0"):
                self._handle_key(ch, msvcrt.getwch, loop)
            else:
                self._handle_key(ch, None, loop)

    def _handle_key(self, ch, next_key, loop):
        """One keypress; next_key supplies the following byte for escapes."""
        if ch in ("\x00", "\xe0"):
            code = next_key() if next_key else ""
            if code == "I":                   # pgup: page up
                self.scroll += 10
            elif code == "Q":                 # pgdn: page down
                self.scroll = max(0, self.scroll - 10)
            elif code == "H":                 # arrow up: line scroll
                self.scroll += 2
            elif code == "P":                 # arrow down: line scroll
                self.scroll = max(0, self.scroll - 2)
            elif code == "G":                 # home: jump to oldest
                self.scroll = 1 << 30
            elif code == "O":                 # end: back to live tail
                self.scroll = 0
            else:
                return
            self.dirty = True
            return
        if ch == "\r":                        # enter
            line, self.buf = self.buf, ""
            self.dirty = True
            loop.call_soon_threadsafe(self._push, line)
        elif ch in ("\x08", "\x7f"):          # backspace
            self.buf = self.buf[:-1]
            self.dirty = True
        elif ch in ("\x03", "\x04"):          # ctrl+c / ctrl+d -> quit
            self.buf = ""
            loop.call_soon_threadsafe(self._push, "/bye")
        elif ch == "\x0c":                    # ctrl+l -> clear pane
            del self.entries[:]
            self.dirty = True
        elif ch.isprintable():
            self.buf += ch
            self.dirty = True

# ---------------------------------------------------------------- entry
async def ui_main(node: Node, ident: Identity, geohash: str | None,
                  tui: bool = False):
    ui = UI(node, ident)
    try:
        await ui.run(geohash, tui=tui)
    finally:
        await node.stop()

def main():
    ap = argparse.ArgumentParser(
        description="bitchat CLI - official-app compatible geochat over Nostr")
    ap.add_argument("--nick", help="nickname (persisted, max 15 chars)")
    ap.add_argument("--geo", "--geohash", dest="geo",
                    help="geohash or 'lat,lon[,level]' to join at startup")
    ap.add_argument("--selftest", action="store_true",
                    help="offline + live protocol tests, then exit")
    ap.add_argument("--sniff", metavar="GEOHASH",
                    help="watch a geohash channel and print raw traffic")
    ap.add_argument("--seconds", type=float, default=30,
                    help="duration for --sniff (default 30)")
    ap.add_argument("--verbose", action="store_true", help="debug output")
    ap.add_argument("--relays", default=None, metavar="URLS",
                    help="comma-separated relay URLs to use instead of the "
                         "auto-nearest set (persisted via /set relays)")
    ap.add_argument("--boost-relays", default=None, metavar="URLS",
                    help="extra relay URLs to also publish through "
                         "(persisted via /set boost)")
    ap.add_argument("--proxy", default=None, metavar="URL",
                    help="http:// or socks5:// proxy, e.g. "
                         "socks5://127.0.0.1:9050 for Tor (persisted via /set)")
    ap.add_argument("--tui", action="store_true",
                    help="alternate-screen UI: message pane + status bar + "
                         "input line (PageUp/PageDown or arrow keys scroll "
                         "history; Home oldest page, End live tail)")
    args = ap.parse_args()

    global VERBOSE
    VERBOSE = args.verbose

    # verify workers do pure-python point math (GIL-bound); short GIL slices
    # keep the asyncio loop responsive while they run
    sys.setswitchinterval(0.001)

    if args.relays:
        SETTINGS["relays"] = [u for u in (_relay_url(x.strip())
                              for x in args.relays.split(",")) if u]
    if getattr(args, "boost_relays", None):
        SETTINGS["boost_relays"] = [u for u in (_relay_url(x.strip())
                                    for x in args.boost_relays.split(",")) if u]
    if args.proxy is not None:
        p = "" if args.proxy.lower() in ("off", "none", "") else args.proxy
        SETTINGS["proxy"] = p if re.match(r"^(https?|socks[45h])://", p, re.I) else ""

    if args.selftest:
        offline_tests()
        try:
            asyncio.run(selftest_live())
        except Exception as e:
            log(red(f"  FAIL live test crashed: {type(e).__name__}: {e}"))
            RESULTS.append(False)
        all_ok = all(RESULTS) and bool(RESULTS)
        print()
        print(green("SELFTEST: ALL PASS") if all_ok
              else red("SELFTEST: FAILURES"))
        raise SystemExit(0 if all_ok else 1)

    if args.sniff:
        asyncio.run(run_sniff(args.sniff, args.seconds))
        raise SystemExit(0)

    # refresh the relay csv in the background: a fresh/stale-network fetch
    # must never delay startup, and the response is closed properly
    threading.Thread(target=refresh_relay_csv_quiet, daemon=True).start()
    ident = Identity.load_or_create()
    if args.nick:
        ident.nick = args.nick.strip()[:MAX_NICK_LEN]

    geo = args.geo or ident.state.get("geohash")
    if geo and "," in geo:
        parts = geo.split(",")
        try:
            prec = int(parts[2]) if len(parts) > 2 else 7
        except ValueError:
            prec = 7
        geo = geohash_encode(float(parts[0]), float(parts[1]), prec)

    node = Node(ident.seed, ident.nick, verbose=args.verbose)
    try:
        asyncio.run(ui_main(node, ident, geo, tui=args.tui))
    except KeyboardInterrupt:
        log(dim("\nbye"))

if __name__ == "__main__":
    main()
