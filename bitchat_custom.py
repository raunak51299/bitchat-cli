#!/usr/bin/env python3
"""
bitchat-cli — an internet-only CLI messenger inspired by bitchat.

No BLE mesh, no central server: messages travel over public Nostr relays as
ephemeral (kind 20001) events — the internet analogue of bitchat's mesh
packets. Public channels are unencrypted (by design, like the mesh).
Direct messages are end-to-end encrypted: ephemeral X25519 → HKDF →
AES-256-GCM, with the sender authenticated by a BIP-340 schnorr signature
inside the ciphertext. Your identity (npub keypair) lives only in
~/.bitchat-cli and keys never leave your machine.

Usage:
    python bitchat.py [--nick NAME] [--relay URL ...] [--channel #bitchat]
                      [--no-colors] [--no-verify] [--selftest]

Everything is ephemeral, like the mesh: messages reach peers that are online
at the same time; nothing is stored or replayed later.
"""
from __future__ import annotations

import argparse
import asyncio
import base64
import hashlib
import hmac
import json
import os
import queue
import secrets
import sys
import threading
import time
import traceback
from collections import deque
from pathlib import Path

try:
    import websockets
except ImportError:
    print("missing dependency — run:  pip install -r requirements.txt", file=sys.stderr)
    sys.exit(1)


def _dbg(*a):
    """Breadcrumbs for best-effort (exception-swallowing) paths; set
    BITCHAT_DEBUG=1 to see them on stderr."""
    if os.environ.get("BITCHAT_DEBUG"):
        print("   ·", *a, file=sys.stderr, flush=True)

if os.name == "nt":
    os.system("")  # enables ANSI escape sequences on legacy Windows consoles

import secp  # local module: BIP-340 schnorr (validated against official vectors)

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.x25519 import (
    X25519PrivateKey, X25519PublicKey,
)
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

# ---------------------------------------------------------------------------
# constants / paths
# ---------------------------------------------------------------------------
PROTOCOL_TAG = "bitchat"       # narrows Nostr subscriptions: #t = <this>
KIND = 20001                   # ephemeral event kind — relays must not store it
DEFAULT_CHANNEL = "#bitchat"

DEFAULT_RELAYS = [
    "wss://nos.lol",
    "wss://nostr.mom",
    "wss://relay.primal.net",
    "wss://relay.snort.social",
]

DATA_DIR = Path.home() / ".bitchat-cli"
IDENTITY_FILE = DATA_DIR / "identity.json"
CONFIG_FILE = DATA_DIR / "config.json"

MAX_TEXT = 2048

PALETTE = (36, 96, 94, 92, 34, 95, 33, 97, 91, 93)

HELP_TEXT = """\
commands:
  /join <#chan>       join a channel (typing goes to the current one)
  /leave [chan]       leave a channel
  /sw <#chan>         switch the current channel
  /msg <nick> <text>  encrypted direct message to a peer
  /msg <hex8> <text>  ...same, using the short id from /who
  /r <text>           reply to the last DM sender
  /nick <name>        change your public nickname
  /who                list peers seen since you started
  /key                show your npub / pubkey
  /relays             relay status
  /relay <wss://...>  add a relay (persisted)
  /clear              clear the screen
  /quit               exit"""

# ---------------------------------------------------------------------------
# bech32 (for npub), minimal
# ---------------------------------------------------------------------------
_B32 = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
_B32_GEN = (0x3B6A57B2, 0x26508E6D, 0x1EA119FA, 0x3D4233DD, 0x2A1462B3)


def _bech32_polymod(values):
    chk = 1
    for v in values:
        b = chk >> 25
        chk = (chk & 0x1FFFFFF) << 5 ^ v
        for i in range(5):
            chk ^= _B32_GEN[i] if ((b >> i) & 1) else 0
    return chk


def _bech32_expand(hrp: str):
    return [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]


def _convert_bits(data, frombits, tobits):
    acc, bits, out = 0, 0, []
    for b in data:
        acc = (acc << frombits) | b
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            out.append((acc >> bits) & ((1 << tobits) - 1))
    if bits:
        out.append((acc << (tobits - bits)) & ((1 << tobits) - 1))
    return out


def npub_encode(xonly32: bytes) -> str:
    data = _convert_bits(xonly32, 8, 5)
    polymod = _bech32_polymod(_bech32_expand("npub") + data + [0] * 6) ^ 1
    checksum = [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]
    return "npub1" + "".join(_B32[d] for d in data + checksum)


# ---------------------------------------------------------------------------
# identity
# ---------------------------------------------------------------------------
class Identity:
    """Local key material. secp256k1 (nostr identity/signing) + X25519 (DMs).

    Persistent only when data_dir == DATA_DIR; otherwise ephemeral (selftest).
    """

    def __init__(self, data_dir: Path = DATA_DIR):
        self.data_dir = Path(data_dir)
        self.persistent = self.data_dir == DATA_DIR
        self._file = self.data_dir / "identity.json"
        self.secp_secret = secp.new_secret()
        self.pub_xonly, self._sign_secret = secp.pubkey_xonly(self.secp_secret)
        self.nick = "anon" + hashlib.sha256(self.pub_xonly).hexdigest()[:4]
        self.x25_priv = os.urandom(32)
        self.loaded = False
        if self.persistent and self._file.exists():
            self.loaded = self._load()

    def _load(self) -> bool:
        try:
            raw = json.loads(self._file.read_text())
            self.secp_secret = bytes.fromhex(raw["secp_secret"])
            self.pub_xonly, self._sign_secret = secp.pubkey_xonly(self.secp_secret)
            self.nick = (raw.get("nick") or "").strip() or self.nick
            self.x25_priv = bytes.fromhex(raw["x25_priv"])
            assert len(self.x25_priv) == 32 and len(self.secp_secret) == 32
            return True
        except Exception as e:
            _dbg("identity load failed, new identity:", type(e).__name__, e)
            return False

    def save(self):
        if not self.persistent:
            return
        self._file.parent.mkdir(parents=True, exist_ok=True)
        self._file.write_text(json.dumps({
            "secp_secret": self.secp_secret.hex(),
            "nick": self.nick,
            "x25_priv": self.x25_priv.hex(),
        }, indent=2))
        try:
            os.chmod(self._file, 0o600)
        except OSError:
            pass

    @property
    def pub_hex(self) -> str:
        return self.pub_xonly.hex()

    def npub(self) -> str:
        return npub_encode(self.pub_xonly)

    def x25_pub_hex(self) -> str:
        from cryptography.hazmat.primitives import serialization
        from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
        key = X25519PrivateKey.from_private_bytes(self.x25_priv)
        return key.public_key().public_bytes(
            serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()

    def set_nick(self, nick: str):
        self.nick = nick.strip()[:24] or self.nick
        self.save()

    def sign_raw(self, digest32: bytes) -> str:
        return secp.sign(self._sign_secret, digest32).hex()


# ---------------------------------------------------------------------------
# DM cryptography (ephemeral X25519 → static recipient X25519 → HKDF → AESGCM)
# ---------------------------------------------------------------------------
_SALT = hashlib.sha256(b"bitchat-cli/v1").digest()


def _hkdf(ikm: bytes, info: bytes = b"dm", length: int = 32) -> bytes:
    prk = hmac.new(_SALT, ikm, hashlib.sha256).digest()
    out, t, i = b"", b"", 1
    while len(out) < length:
        t = hmac.new(prk, t + info + bytes([i]), hashlib.sha256).digest()
        out += t
        i += 1
    return out[:length]


def rtag_for(x25_pub_hex: str) -> str:
    """Lets the intended recipient spot DMs addressed to them without leaking
    anything else (hash of the recipient's public key only)."""
    return hashlib.sha256(bytes.fromhex(x25_pub_hex)).hexdigest()[:16]


def dm_sig_digest(eph_pub_hex: str, rtag: str, ts: int, text: str) -> bytes:
    """Signed by the sender's identity key inside the DM; proves the claimed
    sender authored this DM."""
    return hashlib.sha256(eph_pub_hex.encode() + rtag.encode() +
                          str(int(ts)).encode() + text.encode("utf-8")).digest()


def dm_seal(sender: Identity, recipient_x25_hex: str, text: str):
    """Build a ready-to-publish DM envelope."""
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM

    rtag = rtag_for(recipient_x25_hex)
    ts = int(time.time() * 1000)
    eph = X25519PrivateKey.generate()
    ssk = eph.exchange(
        X25519PublicKey.from_public_bytes(bytes.fromhex(recipient_x25_hex)))
    eph_pub_hex = eph.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()
    inner = {"v": 1, "t": "dmi", "ts": ts, "from": sender.pub_hex,
             "nick": sender.nick, "text": text,
             "sig": sender.sign_raw(dm_sig_digest(eph_pub_hex, rtag, ts, text))}
    nonce = os.urandom(12)
    ct = AESGCM(_hkdf(ssk)).encrypt(nonce, json.dumps(
        inner, separators=(",", ":"), ensure_ascii=False).encode("utf-8"),
        rtag.encode())
    return {"v": 1, "t": "dm", "id": secrets.token_hex(8), "ts": ts,
            "eph": eph_pub_hex, "rt": rtag,
            "ct": base64.b64encode(nonce + ct).decode()}, ts


def dm_open(own_x25_priv: bytes, env: dict):
    """Decrypt a DM envelope. Returns inner dict or None."""
    from cryptography.hazmat.primitives.asymmetric.x25519 import (
        X25519PrivateKey, X25519PublicKey,
    )
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    try:
        rtag = env["rt"]
        ssk = X25519PrivateKey.from_private_bytes(own_x25_priv).exchange(
            X25519PublicKey.from_public_bytes(bytes.fromhex(env["eph"])))
        blob = base64.b64decode(env["ct"])
        nonce, ct = blob[:12], blob[12:]
        plaintext = AESGCM(_hkdf(ssk)).decrypt(nonce, ct, rtag.encode())
        inner = json.loads(plaintext.decode("utf-8"))
        digest = dm_sig_digest(env["eph"], rtag, inner.get("ts", 0),
                               inner.get("text", ""))
        sig = bytes.fromhex(inner.get("sig", ""))
        if not secp.verify(bytes.fromhex(inner.get("from", "")), digest, sig):
            _dbg("dm_open: sender signature failed")
            return None
        return inner
    except Exception as e:
        _dbg("dm_open decrypt refused:", type(e).__name__, e)
        return None


# ---------------------------------------------------------------------------
# envelope → signed Nostr event (NIP-01)
# ---------------------------------------------------------------------------
def envelope_event(identity: Identity, env: dict, p_tag: str | None = None) -> dict:
    content = base64.b64encode(
        json.dumps(env, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    ).decode("ascii")
    created_at = int(env.get("ts", time.time() * 1000) // 1000)
    tags = [["t", PROTOCOL_TAG]]
    if p_tag:
        tags.append(["p", p_tag])
    payload = json.dumps(
        [0, identity.pub_hex, created_at, KIND, tags, content],
        separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    eid = hashlib.sha256(payload).digest()
    return {"id": eid.hex(), "pubkey": identity.pub_hex, "created_at": created_at,
            "kind": KIND, "tags": tags, "content": content,
            "sig": identity.sign_raw(eid)}


# ---------------------------------------------------------------------------
# relay node
# ---------------------------------------------------------------------------
class Node:
    def __init__(self, identity: Identity, relays, on_envelope=None,
                 on_relay=None, no_verify=False, presence_interval=45.0):
        self.identity = identity
        self.no_verify = no_verify
        self.presence_interval = presence_interval
        self.on_envelope = on_envelope            # (env, event_pubkey)
        self.on_relay = on_relay                  # (url, state)
        self.relay_state: dict[str, str] = {}
        self._tasks: list[asyncio.Task] = []
        for u in dict.fromkeys(relays):
            self._register_relay(u)
        self.scheduled: deque = deque()
        self.seen: set[str] = set()
        self.get_chans = lambda: []
        self._stop = False

    def _register_relay(self, url: str):
        self.relay_state[url] = "connecting"

    def add_relay(self, url: str):
        """Register now; spawns a task immediately if the node already runs."""
        if url in self.relay_state:
            return
        self._register_relay(url)
        if self._tasks:
            try:
                loop = asyncio.get_running_loop()
                self._tasks.append(loop.create_task(self._relay_loop(url)))
            except RuntimeError:
                pass  # not running yet; will start on run()

    async def run(self):
        tasks = [asyncio.create_task(self._relay_loop(url))
                 for url in list(self.relay_state)]
        tasks.append(asyncio.create_task(self._presence_loop()))
        self._tasks = tasks
        try:
            await asyncio.gather(*tasks)
        except asyncio.CancelledError:
            pass
        finally:
            for t in tasks:
                if not t.done():
                    t.cancel()

    async def stop(self):
        self._stop = True
        tasks = list(self._tasks)
        for t in tasks:
            t.cancel()
        if tasks:
            await asyncio.gather(*tasks, return_exceptions=True)

    def publish(self, env: dict, p_tag: str | None = None):
        event = envelope_event(self.identity, env, p_tag)
        self.seen.add(event["id"])
        self.scheduled.append(event)

    def _relay_state(self, url: str, state: str):
        if self.relay_state.get(url) == state:
            return
        self.relay_state[url] = state
        if self.on_relay:
            try:
                self.on_relay(url, state)
            except Exception as e:
                _dbg(f"on_relay callback failed for {url}: {e}")

    async def _relay_loop(self, url: str):
        backoff = 2.0
        while not self._stop:
            try:
                async with websockets.connect(url, open_timeout=10,
                                              max_size=2**20, ping_interval=30) as ws:
                    self._relay_state(url, "online")
                    backoff = 2.0
                    since = int(time.time()) - 2
                    await ws.send(json.dumps(["REQ", "bit-all",
                        {"kinds": [KIND], "#t": [PROTOCOL_TAG], "since": since}]))
                    await ws.send(json.dumps(["REQ", "bit-dm",
                        {"kinds": [KIND], "#p": [self.identity.pub_hex],
                         "since": since}]))
                    while not self._stop:
                        while self.scheduled:
                            try:
                                await ws.send(json.dumps(["EVENT", self.scheduled[0]]))
                                self.scheduled.popleft()
                            except websockets.exceptions.ConnectionClosed:
                                self.scheduled.rotate(-1)   # retry after reconnect
                                raise
                        try:
                            raw = await asyncio.wait_for(ws.recv(), timeout=0.25)
                        except asyncio.TimeoutError:
                            continue
                        self._on_relay_message(raw)
            except asyncio.CancelledError:
                raise
            except Exception:
                self._relay_state(url, f"down ({traceback.format_exc(limit=0)[-30:]})"
                                  if os.environ.get("BITCHAT_DEBUG") else "down")
            if not self._stop:
                await asyncio.sleep(backoff)
                backoff = min(backoff * 2, 30)

    async def _presence_loop(self):
        while not self._stop:
            env = {"v": 1, "t": "ann", "id": secrets.token_hex(8),
                   "ts": int(time.time() * 1000),
                   "from": self.identity.pub_hex, "nick": self.identity.nick,
                   "x25": self.identity.x25_pub_hex(),
                   "chans": list(self.get_chans())}
            self.publish(env)
            await asyncio.sleep(self.presence_interval)

    def _on_relay_message(self, raw):
        try:
            msg = json.loads(raw)
        except ValueError:
            return
        if not (isinstance(msg, list) and msg and msg[0] == "EVENT" and len(msg) >= 3):
            return
        ev = msg[2]
        if not isinstance(ev, dict) or ev.get("kind") != KIND:
            return
        if ev.get("id") in self.seen:
            return
        try:
            content = ev["content"]
            payload = json.dumps(
                [0, ev["pubkey"], ev["created_at"], ev["kind"], ev["tags"], content],
                separators=(",", ":"), ensure_ascii=False).encode("utf-8")
            env = json.loads(base64.b64decode(content).decode("utf-8"))
        except Exception as e:
            _dbg("envelope decode failed:", type(e).__name__, e)
            return
        if not self.no_verify:
            if hashlib.sha256(payload).hexdigest() != ev.get("id"):
                return
            try:
                if not secp.verify(bytes.fromhex(ev["pubkey"]), bytes.fromhex(ev["id"]),
                                   bytes.fromhex(ev.get("sig", ""))):
                    return
            except Exception as e:
                _dbg("verify crashed:", type(e).__name__, e)
                return
        if len(self.seen) > 99_999:
            self.seen.clear()
        self.seen.add(ev["id"])
        if self.on_envelope:
            try:
                self.on_envelope(env, ev["pubkey"])
            except Exception:
                if os.environ.get("BITCHAT_DEBUG"):
                    traceback.print_exc()


# ---------------------------------------------------------------------------
# UI
# ---------------------------------------------------------------------------
class UI:
    def __init__(self, identity: Identity, node: Node):
        self.idy = identity
        self.node = node
        self.colors = True
        self.joined = [DEFAULT_CHANNEL]
        self.current = DEFAULT_CHANNEL
        self.peers: dict[str, dict] = {}
        self.last_dm_pub: str | None = None
        self.line_q: queue.Queue = queue.Queue()
        self._done = False
        node.get_chans = lambda: list(self.joined)
        node.on_envelope = self.on_envelope
        node.on_relay = self.on_relay

    # ---- config ----
    def load_config(self, extra_relays=None):
        try:
            cfg = json.loads(CONFIG_FILE.read_text())
        except (OSError, ValueError):
            cfg = {}
        chans = [c if c.startswith("#") else "#" + c
                 for c in (cfg.get("channels") or [])]
        chans = [c for c in chans if self._valid_chan(c)]
        if chans:
            self.joined = chans
            if self.current not in self.joined:
                self.current = self.joined[0]
        for u in cfg.get("relays") or []:
            if isinstance(u, str) and u.startswith("wss://"):
                self.node.add_relay(u)
        for u in extra_relays or []:
            self.node.add_relay(u)

    def save_config(self):
        try:
            DATA_DIR.mkdir(parents=True, exist_ok=True)
            try:
                cfg = json.loads(CONFIG_FILE.read_text())
            except (OSError, ValueError):
                cfg = {}
            cfg["channels"] = list(self.joined)
            cfg["relays"] = list(self.node.relay_state)
            CONFIG_FILE.write_text(json.dumps(cfg, indent=2))
        except OSError as e:
            _dbg("config save failed:", e)

    # ---- printing ----
    def _c(self, s: str, code: int) -> str:
        return f"\x1b[{code}m{s}\x1b[0m" if self.colors else s

    def _nick_render(self, nick: str, pub: str) -> str:
        color = PALETTE[int.from_bytes(hashlib.sha256(pub.encode()).digest()[:2],
                                       "big") % len(PALETTE)]
        return self._c(nick or "?", color)

    def _prompt(self):
        print(self._c(f"[{self.current}] ", 90) + self._c("» ", 92), end="",
              flush=True)

    def sys(self, text: str, redraw=True):
        print(f"{self._c('·', 90)} {text}", flush=True)
        if redraw:
            self._prompt()

    def _ts(self) -> str:
        return self._c(time.strftime("%H:%M:%S") + " ", 90)

    def print_room(self, chan: str, nick: str, pub: str, text: str, own=False):
        room = self._c(f"[{chan}]", 93)
        who = self._c("you", 92) if own else self._nick_render(nick, pub)
        print(f"{self._ts()}{room} {who}{self._c('▸', 90)} {text}", flush=True)
        self._prompt()

    def print_dm(self, nick: str, pub: str, text: str, outgoing=False):
        tag = self._c("dm →", 95) if outgoing else self._c("dm ←", 95)
        who = self._c("you", 92) if outgoing else self._nick_render(nick, pub)
        print(f"{self._ts()}{tag} {who}{self._c('▸', 90)} {text}"
              + ("" if outgoing else "\a"), flush=True)
        self._prompt()

    # ---- relay status callback ----
    def on_relay(self, url: str, state: str):
        short = url.replace("wss://", "")
        if state == "online":
            online = [s for s in self.node.relay_state.values() if s == "online"]
            if len(online) == 1:                      # first one to connect
                self.sys(f"{self._c('online', 92)} on {short} — say hi in "
                         f"{self._c(self.current, 93)}", redraw=True)
            else:
                self.sys(f"{self._c('·', 90)} {short} online",
                         redraw=False)
        else:
            self.sys(f"{self._c(short, 90)} {state}", redraw=False)

    # ---- inbound ----
    def on_envelope(self, env, ev_pub):
        t = env.get("t")
        if t == "ann":
            self._on_announce(env)
        elif t == "msg":
            pub = env.get("from", "")
            if pub != ev_pub:                 # nick claim must match signed identity
                return
            chan = env.get("ch", "")
            if chan in self.joined:
                self.print_room(chan, env.get("nick", "?"), pub,
                                env.get("text", ""), own=False)
        elif t == "dm":
            self._on_dm(env)

    def _on_announce(self, env):
        pub = env.get("from") or ""
        if len(pub) != 64:
            return
        now = time.time()
        rec = self.peers.get(pub)
        fresh = rec is None
        if not rec:
            rec = self.peers[pub] = {}
        rec.update({"nick": env.get("nick") or rec.get("nick", "?"),
                    "x25": env.get("x25") or rec.get("x25", ""),
                    "chans": set(env.get("chans") or []),
                    "last": now})
        for p, r in list(self.peers.items()):          # 15-minute liveness window
            if now - r["last"] > 900:
                del self.peers[p]
        if fresh and (rec["chans"] & set(self.joined)):
            mine = ", ".join(sorted(rec["chans"] & set(self.joined)))
            self.sys(f"{self._nick_render(rec['nick'], pub)} "
                     f"{self._c('connected in', 90)} {self._c(mine, 90)}",
                     redraw=False)

    def _on_dm(self, env):
        if env.get("rt") != rtag_for(self.idy.x25_pub_hex()):
            return                                     # not addressed to us
        inner = dm_open(self.idy.x25_priv, env)
        if not inner:
            self.sys(self._c("dropped a DM that failed verification", 90),
                     redraw=False)
            return
        self.last_dm_pub = inner.get("from")
        nick = inner.get("nick") or (self.peers.get(inner.get("from"))
                                     or {}).get("nick", "?")
        self.print_dm(nick, inner.get("from", ""), inner.get("text", ""),
                      outgoing=False)

    # ---- sending ----
    def send_room(self, chan: str, text: str):
        if not text or not chan or len(text) > MAX_TEXT:
            return
        env = {"v": 1, "t": "msg", "id": secrets.token_hex(8),
               "ts": int(time.time() * 1000), "from": self.idy.pub_hex,
               "nick": self.idy.nick, "ch": chan, "text": text}
        self.node.publish(env)
        self.print_room(chan, self.idy.nick, self.idy.pub_hex, text, own=True)

    def send_dm(self, pub: str, text: str):
        peer = self.peers.get(pub)
        if not peer or not peer.get("x25"):
            self.sys("that peer hasn't been online recently — wait for their "
                     "next ping, or check /who")
            return
        env, _ts = dm_seal(self.idy, peer["x25"], text[:MAX_TEXT])
        self.node.publish(env, p_tag=pub)
        self.print_dm(peer.get("nick", "?"), pub, text, outgoing=True)

    def announce_now(self):
        self.node.publish(self._announce_env())

    def _announce_env(self):
        return {"v": 1, "t": "ann", "id": secrets.token_hex(8),
                "ts": int(time.time() * 1000), "from": self.idy.pub_hex,
                "nick": self.idy.nick, "x25": self.idy.x25_pub_hex(),
                "chans": list(self.joined)}

    # ---- input thread ----
    def run_input(self):
        while not self._done:
            try:
                line = input(self._c(f"[{self.current}] ", 90) + self._c("» ", 92))
            except (EOFError, KeyboardInterrupt):
                self.line_q.put(None)
                return
            if line.strip():
                self.line_q.put(line)

    # ---- commands ----
    def handle(self, line):
        if line is None:
            self._done = True
            return
        s = line.strip()
        if not s:
            return
        if s.startswith("/"):
            parts = s[1:].split(None, 1)
            cmd = parts[0].lower()
            rest = parts[1] if len(parts) > 1 else ""
            handler = getattr(self, f"_cmd_{cmd}", None)
            if callable(handler):
                handler(rest)
            else:
                self.sys(f"unknown command /{cmd} — try /help")
        else:
            if not self.current:
                self.sys("you're not in a channel — /join #bitchat")
            else:
                self.send_room(self.current, s)

    def _valid_chan(self, chan: str) -> str:
        base = (chan or "").lstrip("#").lower()
        base = "".join(c for c in base if c.isalnum() or c in "-_")[:32]
        return ("#" + base) if base else ""

    def resolve_peer(self, mention: str) -> str | None:
        if not mention:
            return None
        if not self.peers:
            self.sys("no peers connected yet — they show up after announcing")
            return None
        nickname = [p for p, r in self.peers.items() if r["nick"].lower() == mention]
        if len(nickname) == 1:
            return nickname[0]
        by_hex = [p for p in self.peers if p.startswith(mention)]
        candidates = nickname if len(nickname) > 1 else by_hex
        if len(candidates) == 1:
            return candidates[0]
        if not candidates:
            self.sys(f"no peer matching '{mention}' — try /who")
        else:
            self.sys(f"'{mention}' matches multiple peers:")
            for p in candidates:
                self.sys(f"  {self.peers[p]['nick']}  {self._c(p[:8], 90)}",
                         redraw=False)
        return None

    def _cmd_help(self, _):
        for ln in HELP_TEXT.splitlines():
            self.sys(ln, redraw=(ln == HELP_TEXT.splitlines()[-1]))

    def _cmd_join(self, rest):
        chan = self._valid_chan(rest)
        if not chan:
            self.sys("usage: /join #channel")
            return
        if chan not in self.joined:
            self.joined.append(chan)
            self.save_config()
        self.current = chan
        self.announce_now()
        self.sys(f"joined {chan}")

    def _cmd_leave(self, rest):
        chan = self._valid_chan(rest) if rest else self.current
        if chan in self.joined:
            self.joined.remove(chan)
            self.save_config()
        if self.current not in self.joined:
            self.current = self.joined[0] if self.joined else ""
        if chan:
            self.sys(f"left {chan}")
        self.announce_now()

    def _cmd_sw(self, rest):
        chan = self._valid_chan(rest)
        if chan in self.joined:
            self.current = chan
            self.sys(f"now in {chan}")
        else:
            self.sys(f"you're not in {chan} — /join it first")

    def _cmd_msg(self, rest):
        parts = (rest or "").split(None, 1)
        if len(parts) < 2 or not parts[1]:
            self.sys("usage: /msg <nick|id8> <text>")
            return
        pub = self.resolve_peer(parts[0].lstrip("@").lower())
        if pub:
            self.send_dm(pub, parts[1])

    def _cmd_r(self, rest):
        if not self.last_dm_pub:
            self.sys("no DM to reply to yet")
        elif rest.strip():
            self.send_dm(self.last_dm_pub, rest)
        else:
            self.sys("usage: /r <text>")

    def _cmd_nick(self, rest):
        if rest.strip():
            self.idy.set_nick(rest.strip())
            self.announce_now()
            self.sys(f"nickname set to '{self.idy.nick}'")
        else:
            self.sys("usage: /nick <name>")

    def _cmd_who(self, _):
        peers = list(self.peers.items())
        if not peers:
            self.sys("no peers yet — peers ping every ~45s; wait a moment")
            return
        now = time.time()
        merged = [p for p in peers if p[1]["chans"] & set(self.joined)]
        self.sys(f"{len(peers)} peers seen ({len(merged)} in your channels)")
        for pub, rec in sorted(peers, key=lambda kv: kv[1]["nick"].lower()):
            chans = ",".join(sorted(rec["chans"])) or "—"
            shared = self._c("◉", 92) if rec["chans"] & set(self.joined) \
                else self._c("○", 90)
            age = str(int(now - rec["last"]) + 1) + "s"
            self.sys(f"{shared} {rec['nick']}  {self._c(pub[:8], 90)}  "
                     f"{self._c('age ' + age, 90)}  {self._c(chans, 90)}",
                     redraw=(rec["nick"] == peers[-1][1]["nick"]))

    def _cmd_key(self, _):
        self.sys(f"npub:  {self.idy.npub()}")
        self.sys(f"hex:   {self.idy.pub_hex}", redraw=False)

    def _cmd_relays(self, _):
        urls = list(self.node.relay_state.items())
        for url, st in urls:
            color = 92 if st == "online" else 91
            self.sys(f"{url}  {self._c('·', color)} {st}",
                     redraw=(url == urls[-1][0]))

    def _cmd_relay(self, rest):
        url = rest.strip().strip("\"'`")
        if not url.startswith("wss://"):
            self.sys("usage: /relay wss://host/path")
            return
        self.node.add_relay(url)
        self.save_config()
        self.sys(f"relay {url} queued")

    def _cmd_clear(self, _):
        os.system("cls" if os.name == "nt" else "clear")
        self._prompt()

    def _cmd_quit(self, _):
        print(self._c("bye ✓", 92), flush=True)
        self._done = True
        self.line_q.put(None)

    _cmd_q = _cmd_exit = _cmd_quit


# ---------------------------------------------------------------------------
# banner + main
# ---------------------------------------------------------------------------
def banner(ui: UI):
    print(ui._c("═" * 64, 36))
    print(ui._c("  bitchat-cli — online mode", 96) +
          ui._c("   (no BLE mesh · no servers)", 90))
    print(ui._c("═" * 64, 36))
    print(f"  identity: {ui._c(ui.idy.nick, 92)}   "
          f"{ui._c(ui.idy.npub()[:20] + '…', 90)}")
    print(f"  channel:  {ui._c(ui.current, 93)}     "
          f"{ui._c('type /help for commands', 90)}")
    print(f"  keys:     {ui._c(str(IDENTITY_FILE), 90)}")
    print(f"  relays:   {ui._c(', '.join(ui.node.relay_state), 90)}")
    print()


def parse_args(argv):
    ap = argparse.ArgumentParser(
        prog="bitchat.py",
        description="bitchat-style chat over public Nostr relays (online mode)")
    ap.add_argument("--nick", help="display nickname")
    ap.add_argument("--channel", "-c",
                    help="initial channel (default: #bitchat, persisted)")
    ap.add_argument("--relay", action="append", default=[],
                    help="extra/override relay URL (repeatable)")
    ap.add_argument("--no-colors", action="store_true")
    ap.add_argument("--no-verify", action="store_true",
                    help="skip signature verification on inbound events (unsafe)")
    ap.add_argument("--selftest", action="store_true",
                    help="run the built-in end-to-end test (needs internet)")
    return ap.parse_args(argv)


async def run_main(args) -> None:
    identity = Identity()
    if not identity.loaded:
        identity.save()
    if args.nick:
        identity.set_nick(args.nick)

    node = Node(identity, list(DEFAULT_RELAYS), no_verify=args.no_verify)
    ui = UI(identity, node)
    ui.colors = not args.no_colors
    ui.load_config(extra_relays=args.relay)

    if args.channel:
        chan = ui._valid_chan(args.channel)
        if chan and chan not in ui.joined:
            ui.joined.append(chan)
            ui.save_config()
        if chan:
            ui.current = chan

    banner(ui)

    loop = asyncio.get_running_loop()
    threading.Thread(target=ui.run_input, daemon=True).start()
    node_task = asyncio.create_task(node.run())
    try:
        while True:
            line = await loop.run_in_executor(None, ui.line_q.get)
            if line is None or ui._done:
                break
            ui.handle(line)
    except KeyboardInterrupt:
        print(ui._c("you disconnected", 90), flush=True)
    finally:
        ui._done = True
        try:
            await asyncio.wait_for(node.stop(), timeout=5)
        except (asyncio.TimeoutError, asyncio.CancelledError, Exception) as e:
            _dbg("node stop:", type(e).__name__, e)
        node_task.cancel()
        try:
            await node_task
        except (asyncio.CancelledError, Exception) as e:
            _dbg("node task end:", type(e).__name__, e)
        ui.save_config()


# ---------------------------------------------------------------------------
# --selftest : two nodes on real relays trade an announcement, a channel
# message and an encrypted DM; plus unit checks for the crypto primitives
# ---------------------------------------------------------------------------
def selftest() -> int:
    import tempfile

    relays = DEFAULT_RELAYS[:3]
    print(f"selftest relays: {', '.join(r.replace('wss://', '') for r in relays)}")
    print("waiting for relay connections and peer announcements…\n")

    id_a = Identity(Path(tempfile.mkdtemp(prefix="bitchat-a-")))
    id_b = Identity(Path(tempfile.mkdtemp(prefix="bitchat-b-")))
    chan = "#bitchat-selftest-" + secrets.token_hex(3)
    boxes = {"a": {"ann": [], "msg": [], "dm": None},
             "b": {"ann": [], "msg": [], "dm": None}}

    def record(box_key):
        own_x25_hex = id_a.x25_pub_hex() if box_key == "a" else id_b.x25_pub_hex()

        def rec(env, ev_pub):
            t = env.get("t")
            if t == "ann":
                boxes[box_key]["ann"].append(env)
            elif t == "msg":
                boxes[box_key]["msg"].append(env)
            elif t == "dm" and env.get("rt") == rtag_for(own_x25_hex):
                boxes[box_key]["dm"] = env
        return rec

    n_a = Node(id_a, relays, on_envelope=record("a"))
    n_b = Node(id_b, relays, on_envelope=record("b"))
    n_a.get_chans = lambda: [chan]
    n_b.get_chans = lambda: [chan]

    failures: list[str] = []

    async def go():
        runs = [asyncio.create_task(n_a.run()), asyncio.create_task(n_b.run())]
        try:
            # stage 1: presence
            ok_ann = False
            for _ in range(25):
                await asyncio.sleep(1)
                heard_b = any(e.get("from") == id_b.pub_hex for e in boxes["a"]["ann"])
                heard_a = any(e.get("from") == id_a.pub_hex for e in boxes["b"]["ann"])
                if heard_a and heard_b:
                    ok_ann = True
                    break
            online = [u for u, s in n_a.relay_state.items() if s == "online"]
            if ok_ann:
                print(f"✓ announce/presence     A↔B  ({len(online)}/{len(relays)} relays online)")
            else:
                print(f"× announce/presence     (relays online: {len(online)}/{len(relays)})")
                failures.append("announce")

            if ok_ann:
                # stage 2: channel message A → B
                env_msg = {"v": 1, "t": "msg", "id": secrets.token_hex(8),
                           "ts": int(time.time() * 1000), "from": id_a.pub_hex,
                           "nick": "tester-a", "ch": chan,
                           "text": "hello over the relays!"}
                n_a.publish(env_msg)
                ok_msg = False
                for _ in range(15):
                    await asyncio.sleep(1)
                    if any(e.get("id") == env_msg["id"] for e in boxes["b"]["msg"]):
                        ok_msg = True
                        break
                print(("✓" if ok_msg else "×") + " channel message A → B")
                if not ok_msg:
                    failures.append("msg")

                # stage 3: encrypted DM A → B
                x25_b = next((e["x25"] for e in boxes["a"]["ann"]
                              if e.get("from") == id_b.pub_hex and e.get("x25")), None)
                if x25_b:
                    env_dm, _ = dm_seal(id_a, x25_b, "secret dm ☺")
                    n_a.publish(env_dm, p_tag=id_b.pub_hex)
                    ok_dm = False
                    for _ in range(15):
                        await asyncio.sleep(1)
                        got = boxes["b"]["dm"]
                        if got:
                            inner = dm_open(id_b.x25_priv, got)
                            if inner and inner.get("text") == "secret dm ☺" \
                                    and inner.get("from") == id_a.pub_hex:
                                ok_dm = True
                            break
                    print(("✓" if ok_dm else "×") +
                          " encrypted DM A → B   (X25519+HKDF+AES-GCM, sender signature)")
                    if not ok_dm:
                        failures.append("dm")
                else:
                    print("× encrypted DM A → B   (no X25519 key in B's announce)")
                    failures.append("dm")
        finally:
            for r in runs:
                r.cancel()
            await asyncio.gather(*runs, return_exceptions=True)
            await n_a.stop()
            await n_b.stop()

    asyncio.run(go())

    # quick primitives (relay-independent)
    secret = secp.new_secret()
    xonly, _ = secp.pubkey_xonly(secret)
    digest = hashlib.sha256(b"probe").digest()
    sig = secp.sign(secret, digest)
    prop_ok = secp.verify(xonly, digest, sig)
    a_priv = X25519PrivateKey.from_private_bytes(os.urandom(32))
    a_priv_bytes = a_priv.private_bytes(
        serialization.Encoding.Raw, serialization.PrivateFormat.Raw,
        serialization.NoEncryption())
    a_pub = a_priv.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()
    rtag = rtag_for(a_pub)
    eph_hex, ct_b64 = dm_encrypt_roundtrip(a_pub, b"roundtrip", rtag)
    roundtrip_ok = dm_decrypt(a_priv_bytes, eph_hex, rtag, ct_b64) == b"roundtrip"
    print(("✓" if npub_encode(xonly).startswith("npub1") else "×") +
          " bech32 npub encoding")
    print(("✓" if prop_ok else "×") + " schnorr sign/verify roundtrip")
    print(("✓" if roundtrip_ok else "×") + " DM seal/open roundtrip")
    for name, ok in (("npub", npub_encode(xonly).startswith("npub1")),
                     ("schnorr", prop_ok), ("dm-crypto", roundtrip_ok)):
        if not ok:
            failures.append(name)

    if failures:
        print(f"\nSELFTEST FAILED: {failures}")
        return 1
    print("\nSELFTEST PASSED ✔")
    return 0


def dm_encrypt_roundtrip(recipient_x25_hex: str, plaintext: bytes, rtag: str):
    """Standalone seal used by the selftest to check raw byte roundtrips."""
    eph = X25519PrivateKey.generate()
    ssk = eph.exchange(X25519PublicKey.from_public_bytes(
        bytes.fromhex(recipient_x25_hex)))
    nonce = os.urandom(12)
    ct = AESGCM(_hkdf(ssk)).encrypt(nonce, plaintext, rtag.encode())
    eph_pub_hex = eph.public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw).hex()
    return eph_pub_hex, base64.b64encode(nonce + ct).decode()


def dm_decrypt(own_x25_priv, eph_pub_hex: str, rtag: str, b64_blob: str):
    from cryptography.hazmat.primitives.asymmetric.x25519 import (
        X25519PrivateKey, X25519PublicKey,
    )
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    try:
        ssk = X25519PrivateKey.from_private_bytes(own_x25_priv).exchange(
            X25519PublicKey.from_public_bytes(bytes.fromhex(eph_pub_hex)))
        blob = base64.b64decode(b64_blob)
        nonce, ct = blob[:12], blob[12:]
        return AESGCM(_hkdf(ssk)).decrypt(nonce, ct, rtag.encode())
    except Exception as e:
        _dbg("dm_decrypt refused:", type(e).__name__, e)
        return None


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except Exception as e:
            _dbg("stdout reconfigure skipped:", e)
    args = parse_args(sys.argv[1:])
    if args.selftest:
        try:
            return selftest()
        except KeyboardInterrupt:
            print("\ninterrupted")
            return 130
    try:
        asyncio.run(run_main(args))
        return 0
    except KeyboardInterrupt:
        print("\nbye")
        return 0


if __name__ == "__main__":
    sys.exit(main())
