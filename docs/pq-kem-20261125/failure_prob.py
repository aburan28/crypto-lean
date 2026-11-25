#!/usr/bin/env python3
"""Decryption-failure probability of ML-KEM (FIPS 203), recomputed from scratch.

Independent re-derivation of the delta in FIPS 203 Table 1, with the noise model of
the Kyber round-3 analysis script: per coefficient, the decryption noise is

    w = <e, r> + e2 + c_v - <s, e1 + c_u>          (CryptoLean.PQ.decrypt_encrypt)

with s, e, r ~ B_eta1, e1, e2 ~ B_eta2, and c_u, c_v the Compress/Decompress rounding
errors for d_u, d_v (u, v modelled as uniform mod q). Coefficients of polynomial
products are sums of k*256 independent coefficient products (the standard heuristic).
Decoding returns the right bit whenever |w| < 832 (CryptoLean.Lattice.mlkem_decode_correct),
so a coefficient fails with probability at most P[|w| >= 832], and a 256-bit message
fails with probability at most 256 * P[|w| >= 832] (union bound).

Distributions are exact over Z_q (cyclic convolution of probability vectors in double
precision; all entries are non-negative so the tail has small relative error).
"""
import math
import numpy as np

Q = 3329
PARAMS = {  # name: (k, eta1, eta2, du, dv)
    "ML-KEM-512": (2, 3, 2, 10, 4),
    "ML-KEM-768": (3, 2, 2, 10, 4),
    "ML-KEM-1024": (4, 2, 2, 11, 5),
}
FIPS203_LOG2_DELTA = {"ML-KEM-512": -138.8, "ML-KEM-768": -164.8, "ML-KEM-1024": -174.8}


def vec(d):
    v = np.zeros(Q)
    for x, p in d.items():
        v[x % Q] += p
    return v


def cbd(eta):
    d = {}
    for a in range(2 ** eta):
        for b in range(2 ** eta):
            x = bin(a).count("1") - bin(b).count("1")
            d[x] = d.get(x, 0) + 1 / 4 ** eta
    return d


def compress_err(dbits):
    """Distribution of Decompress_d(Compress_d(x)) - x (centred) for x uniform mod q."""
    d = {}
    for x in range(Q):
        y = ((2 ** dbits * 2 * x + Q) // (2 * Q)) % 2 ** dbits       # FIPS 203 (4.7)
        z = (2 * Q * y + 2 ** dbits) // (2 ** dbits * 2)             # FIPS 203 (4.8)
        e = (z - x) % Q
        e = e - Q if e > Q // 2 else e
        d[e] = d.get(e, 0) + 1 / Q
    return d


def conv(a, b):
    c = np.convolve(a, b)
    out = c[:Q].copy()
    out[: len(c) - Q] += c[Q:]
    return out


def power(v, n):
    r = vec({0: 1.0})
    while n:
        if n & 1:
            r = conv(r, v)
        v = conv(v, v)
        n >>= 1
    return r


def product(d1, d2):
    d = {}
    for a, p in d1.items():
        for b, s in d2.items():
            d[a * b] = d.get(a * b, 0) + p * s
    return d


def add(d1, d2):
    d = {}
    for a, p in d1.items():
        for b, s in d2.items():
            d[a + b] = d.get(a + b, 0) + p * s
    return d


def delta(k, eta1, eta2, du, dv):
    b1, b2 = cbd(eta1), cbd(eta2)
    er = vec(product(b1, b1))                    # e_i * r_i
    s_e1cu = vec(product(b1, add(b2, compress_err(du))))   # s_i * (e1 + c_u)_i
    n = k * 256
    w = conv(conv(power(er, n), power(s_e1cu, n)), vec(add(b2, compress_err(dv))))
    # w and -w have the same law (all inputs are symmetric), so the sign of the s-term is immaterial.
    tail = sum(w[x % Q] for x in range(-(Q // 2), Q // 2 + 1) if abs(x) >= 832)
    return tail, 256 * tail


if __name__ == "__main__":
    print(f"{'set':12s} {'log2 P[coef]':>13s} {'log2 delta (union)':>19s} {'FIPS 203':>9s}")
    for name, p in PARAMS.items():
        t, dl = delta(*p)
        print(f"{name:12s} {math.log2(t):13.1f} {math.log2(dl):19.1f} {FIPS203_LOG2_DELTA[name]:9.1f}")
