"""
secp256k1 + BIP-340 Schnorr in pure Python (no external deps).
Enough to make and verify Nostr-compatible event signatures.

Only used for identity keys / event signing. Message encryption uses
X25519 + AES-256-GCM from the `cryptography` package.
"""
import hashlib
import secrets

from cryptography.hazmat.primitives.asymmetric import ec

_CURVE = ec.SECP256K1()

# --- curve parameters (secp256k1) -----------------------------------------
P = 2**256 - 2**32 - 977                # field prime
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141  # order
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = pow((GX * GX * GX + 7) % P, (P + 1) // 4, P)   # even-y point with x = GX
G = (GX, GY)
by = (P + 1) // 4                        # for square roots mod P


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


def _secret_mul_g(d: int):
    """d*G for secret d, via OpenSSL (constant-time, fast)."""
    nums = ec.derive_private_key(d, _CURVE).public_key().public_numbers()
    return (nums.x, nums.y)


def _secret_ecdh_x(d: int, point) -> int:
    """x coordinate of d*point for secret d, via OpenSSL."""
    pub = ec.EllipticCurvePublicNumbers(point[0], point[1], _CURVE).public_key()
    shared = ec.derive_private_key(d, _CURVE).exchange(ec.ECDH(), pub)
    return int.from_bytes(shared, "big")


def lift_x_parity(xonly: bytes, want_odd: bool):
    """lift_x with a chosen y parity (0x02=even / 0x03=odd prefix semantics).
    bitchat/iOS derives NIP-44 keys from the compressed shared point, i.e. the
    y sign matters and the party chooses the lift parity explicitly."""
    x = int.from_bytes(xonly, "big")
    if x >= P:
        return None
    c = (x * x * x + 7) % P
    y = pow(c, by, P)
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
    # Secret-scalar work is done by OpenSSL; OpenSSL's ECDH only returns x, so
    # recover y's sign from a second ECDH against peer+G (all public data).
    other = point_add(peer, G)
    if other is None:
        return None
    x = _secret_ecdh_x(d, peer)
    x2 = _secret_ecdh_x(d, other)
    dG = _secret_mul_g(d)
    y = None
    for cy in _y_candidates(x):
        s_pt = point_add((x, cy), dG)
        if s_pt is not None and s_pt[0] == x2:
            y = cy
            break
    if y is None:
        return None
    return (0x02 if y % 2 == 0 else 0x03).to_bytes(1, "big") + \
        x.to_bytes(32, "big")

def _y_candidates(x: int):
    y = pow((x * x * x + 7) % P, by, P)
    return (y, P - y)


def lift_x(xonly: bytes):
    """BIP-340 lift_x: the even-y point with the given x coordinate."""
    return lift_x_parity(xonly, False)


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
    x, y = _secret_mul_g(d)
    if y % 2:                              # keep pubkey y even (BIP-340)
        d = N - d
    return x.to_bytes(32, "big"), d.to_bytes(32, "big")


def point_xonly(point) -> bytes:
    x, y = point
    return x.to_bytes(32, "big")


def sign(secret32: bytes, msg32: bytes, aux32: bytes = None) -> bytes:
    """BIP-340 sign. msg32 should be the already-hashed message (e.g. event id)."""
    if aux32 is None:
        aux32 = secrets.token_bytes(32)    # BIP-340 recommends fresh aux rand
    xonly, d32 = pubkey_xonly(secret32)
    d = int.from_bytes(d32, "big")
    Pk = lift_x(xonly)
    aux = tagged_hash(b"BIP0340/aux", aux32)
    t = bytes(a ^ b for a, b in zip(d32, aux))
    # NOTE: the nonce hash includes the x-only public key (easy to miss!)
    rand = tagged_hash(b"BIP0340/nonce", t + point_xonly(Pk) + msg32)
    k = int.from_bytes(rand, "big") % N
    if k == 0:
        raise ValueError("nonce failed")
    R = _secret_mul_g(k)
    if R[1] % 2:
        k = N - k
    e = int.from_bytes(tagged_hash(
        b"BIP0340/challenge", point_xonly(R) + point_xonly(Pk) + msg32), "big") % N
    s = (k + e * d) % N
    if s == 0:
        raise ValueError("signature failed")
    sig = point_xonly(R) + s.to_bytes(32, "big")
    if not verify(xonly, msg32, sig):      # belt & braces
        raise ValueError("created signature failed self-verification")
    return sig


def verify(xonly: bytes, msg: bytes, sig: bytes) -> bool:
    """BIP-340 verify. sig must be 64 bytes (r || s), msg may be any length."""
    if len(xonly) != 32 or len(sig) != 64:
        return False
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


def new_secret() -> bytes:
    for _ in range(10):
        s = secrets.token_bytes(32)
        if 1 <= int.from_bytes(s, "big") < N:
            return s
    raise RuntimeError("secret generation failed")
