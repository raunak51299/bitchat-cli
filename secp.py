"""
secp256k1 + BIP-340 Schnorr. Enough to make and verify Nostr-compatible
event signatures.

WARNING (docs): the built-in implementation is PURE PYTHON: it is NOT
constant-time (double-and-add branches on secret bits, and every affine
step does a modular inversion) and it is slow. That is an accepted
trade-off for a hobby CLI: the key involved is a disposable nickname
identity, never a wallet. For timing-sensitive environments install the
libsecp256k1-backed `coincurve` package (`pip install coincurve`) - it
is detected and used automatically when importable and compatible (the
backend is self-checked at import against this module's pure
implementation, so any API drift simply disables it instead of breaking
users). Set SECP_FORCE_PURE_PYTHON=1 to force the pure-python backend.

Only used for identity keys / event signing. Message encryption uses
X25519 + AES-256-GCM from the `cryptography` package.
"""
import hashlib
import os
import secrets

# --- curve parameters (secp256k1) -----------------------------------------
P = 2**256 - 2**32 - 977                # field prime
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141  # order
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = pow((GX * GX * GX + 7) % P, (P + 1) // 4, P)   # even-y point with x = GX
G = (GX, GY)


def _inv(a: int) -> int:
    return pow(a, P - 2, P)


def point_add(p1, p2):
    """Affine point addition. None means the point at infinity."""
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None                       # P1 + (-P1) = O
    if p1 == p2:                          # doubling (y1 != 0 here)
        lam = (3 * x1 * x1) * _inv(2 * y1) % P
    else:
        lam = (y2 - y1) * _inv(x2 - x1) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)


def point_mul(point, k: int):
    k %= N
    if k == 0:
        return None
    result, addend = None, point
    while k:
        if k & 1:
            result = point_add(result, addend)
        addend = point_add(addend, addend)
        k >>= 1
    return result


def lift_x_parity(xonly: bytes, want_odd: bool):
    """lift_x with a chosen y parity (0x02=even / 0x03=odd prefix semantics).
    bitchat/iOS derives NIP-44 keys from the compressed shared point, i.e. the
    y sign matters and the party chooses the lift parity explicitly."""
    x = int.from_bytes(xonly, "big")
    if x >= P:
        return None
    c = (x * x * x + 7) % P
    y = pow(c, (P + 1) // 4, P)
    if (y * y) % P != c:
        return None
    if (y % 2 == 1) != bool(want_odd):
        y = P - y
    return (x, y)


def ecdh_compressed(priv32: bytes, peer_xonly: bytes, want_odd: bool):
    """bitchat/iOS DM secret material: ECDH shared point, returned as the
    33-byte compressed point (parity byte + x32). HKDF runs over these 33
    bytes, NOT the standard 32-byte x-only NIP-44 secret."""
    peer = lift_x_parity(peer_xonly, want_odd)
    if peer is None:
        return None
    d = int.from_bytes(priv32, "big") % N
    if d == 0:
        return None
    pt = point_mul(peer, d)
    if pt is None:
        return None
    x, y = pt
    return (0x02 if y % 2 == 0 else 0x03).to_bytes(1, "big") + \
        x.to_bytes(32, "big")


def lift_x(xonly: bytes):
    """BIP-340 lift_x: the even-y point with the given x coordinate."""
    return lift_x_parity(xonly, want_odd=False)


# --- BIP-340 helpers -------------------------------------------------------
def tagged_hash(tag: bytes, msg: bytes) -> bytes:
    tag_hash = hashlib.sha256(tag).digest()
    return hashlib.sha256(tag_hash + tag_hash + msg).digest()


def pubkey_xonly(secret32: bytes):
    """Returns (xonly_pubkey_bytes, signing_secret32) where the signing secret
    is tweaked so the resulting public key has an even y coordinate."""
    d = int.from_bytes(secret32, "big")
    if not 1 <= d < N:
        raise ValueError("bad secret key")
    pt = point_mul(G, d)
    assert pt is not None
    x, y = pt
    if y % 2:                              # keep pubkey y even (BIP-340)
        d = N - d
    return x.to_bytes(32, "big"), d.to_bytes(32, "big")


def point_xonly(point) -> bytes:
    x, y = point
    return x.to_bytes(32, "big")


def _pure_sign(secret32: bytes, msg32: bytes,
               aux32: bytes = b"\x00" * 32) -> tuple:
    """Reference BIP-340 sign with an explicit aux (test-vector friendly).
    Returns (sig, xonly_pubkey, tweaked_secret) so callers can self-verify
    without recomputing the public key (a full scalar multiplication)."""
    xonly, d32 = pubkey_xonly(secret32)
    d = int.from_bytes(d32, "big")
    aux = tagged_hash(b"BIP0340/aux", aux32)
    t = bytes(a ^ b for a, b in zip(d32, aux))
    # NOTE: the nonce hash includes the x-only public key (easy to miss!).
    # x(Pk) is exactly `xonly`, so no second scalar multiplication is needed.
    rand = tagged_hash(b"BIP0340/nonce", t + xonly + msg32)
    k = int.from_bytes(rand, "big") % N
    if k == 0:
        raise ValueError("nonce failed")
    R = point_mul(G, k)
    assert R is not None
    if R[1] % 2:
        k = N - k
    e = int.from_bytes(tagged_hash(
        b"BIP0340/challenge", point_xonly(R) + xonly + msg32), "big") % N
    s = (k + e * d) % N
    if s == 0:
        raise ValueError("signature failed")
    return point_xonly(R) + s.to_bytes(32, "big"), xonly, d32


def _pure_verify(xonly: bytes, msg: bytes, sig: bytes) -> bool:
    """Reference BIP-340 verify. sig is 64 bytes (r || s)."""
    Pk = lift_x(xonly)
    if Pk is None:
        return False
    r = int.from_bytes(sig[:32], "big")
    s = int.from_bytes(sig[32:], "big")
    if r >= P or s >= N:
        return False
    e = int.from_bytes(tagged_hash(b"BIP0340/challenge",
                                   sig[:32] + xonly + msg), "big") % N
    R = point_add(point_mul(G, s), point_mul(Pk, (N - e) % N))
    if R is None or R[1] % 2:
        return False
    return R[0] == r


# --- optional libsecp256k1 backend (coincurve) -----------------------------
# Activates only after a runtime self-check against the pure implementation,
# so API drift across coincurve versions disables it instead of diverging.
_FORCE_PURE = bool(os.environ.get("SECP_FORCE_PURE_PYTHON"))
HAVE_COINCURVE = False
coincurve = None


def _detect_libsecp_backend():
    """Feature-detect coincurve's BIP-340 API and return (sign, verify) or None."""
    try:
        import coincurve as cc            # noqa: F401 (used via returned wrapper)
        sch = getattr(cc, "Schnorr", None)
        if sch is None or not hasattr(sch, "sign") or not hasattr(sch, "verify"):
            return None
        schnorr = sch()
        sk = new_secret()
        msg = hashlib.sha256(b"secp backend selfcheck").digest()
        xonly, _ = pubkey_xonly(sk)
        aux = secrets.token_bytes(32)
        # every direction must agree with this module's own implementation:
        s_cc = schnorr.sign(msg, sk, aux)
        s_pure, _, _ = _pure_sign(sk, msg, aux)
        if not (verify(xonly, msg, s_cc) and schnorr.verify(s_pure, msg, xonly)
                and schnorr.verify(s_cc, msg, xonly)
                and _pure_verify(xonly, msg, s_pure)):
            return None

        def cc_sign(secret32, msg32, aux32=None):
            return schnorr.sign(msg32, secret32, aux32)

        def cc_verify(xonly, msg32, sig):
            return schnorr.verify(sig, msg32, xonly)

        return cc_sign, cc_verify
    except Exception:
        return None


_BACKEND = None if _FORCE_PURE else _detect_libsecp_backend()
if _BACKEND:
    HAVE_COINCURVE = True
    coincurve = True                      # truthy marker for introspection
    _cc_sign, _cc_verify = _BACKEND


def sign(secret32: bytes, msg32: bytes, aux32: bytes | None = None) -> bytes:
    """BIP-340 sign. msg32 should be the already-hashed message (e.g. event id).
    aux32=None (default) draws fresh randomness, following BIP-340's
    blinding recommendation for side-channel resistance. Signatures stayed
    fully valid (and remain reproducible given the same aux)."""
    if aux32 is None:
        aux32 = secrets.token_bytes(32)
    if HAVE_COINCURVE:
        try:
            sig = _cc_sign(secret32, msg32, aux32)
            xonly, _ = pubkey_xonly(secret32)
            if verify(xonly, msg32, sig):    # belt & braces, backend self-check
                return sig
        except Exception:
            pass                             # documented: fall back to pure python
    sig, xonly, _ = _pure_sign(secret32, msg32, aux32)
    if not verify(xonly, msg32, sig):        # belt & braces
        raise ValueError("created signature failed self-verification")
    return sig


def verify(xonly: bytes, msg: bytes, sig: bytes) -> bool:
    """BIP-340 verify. sig must be 64 bytes (r || s), msg may be any length."""
    if len(xonly) != 32 or len(sig) != 64:
        return False
    if HAVE_COINCURVE:
        try:
            return _cc_verify(xonly, msg, sig)
        except Exception:
            pass                             # documented: fall back to pure python
    return _pure_verify(xonly, msg, sig)


def new_secret() -> bytes:
    for _ in range(10):
        s = secrets.token_bytes(32)
        if 1 <= int.from_bytes(s, "big") < N:
            return s
    raise RuntimeError("secret generation failed")
