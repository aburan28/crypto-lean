"""Exact brute-force check of CryptoLean.ConductorGap on small prime fields.

For every prime p in [P_LO, P_HI], every ordinary F_p-isogeny class with
trace t (t^2 - 4p = D0 f^2, D0 fundamental, D0 not -3/-4) and every odd prime
N with N || f and N | #E = p + 1 - t:

  (A) gap_prime_dvd_order: N | p-1, N | t-2, N^2 | #E.
  (B) crater_side_full / floor_side_line via E[N] = O_c/N O_c (Lenstra):
      each curve has #E(F_p)[N] in {N, N^2}; (Frobenius eigenvalue t/2 = 1).
  (C) the count of curves (j-invariants) with #E(F_p)[N] = N (floor, N | c)
      equals (N - (D0/N)) times the count with N^2 (crater, N not | c),
      as the class-number formula h(O_{cN}) = h(O_c)(N - (D0/N)) predicts
      when O_c^x = {+-1}.
No randomness. Prints one JSON summary line; exit 1 on any failure.
"""
import json, sys
P_LO, P_HI = int(sys.argv[1]) if len(sys.argv) > 1 else 100, int(sys.argv[2]) if len(sys.argv) > 2 else 600

def is_prime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def factor(n):
    n = abs(n); f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def fundamental(delta):  # delta < 0, returns (D0, f)
    fs = factor(delta); f = 1
    for q, e in fs.items(): f *= q ** (e // 2)
    D = delta // (f * f)
    if D % 4 != 1:  # D = 2,3 mod 4 -> 4D fundamental, f halves
        assert f % 2 == 0, (delta, D, f)
        D *= 4; f //= 2
    return D, f

def kron(D, N):  # Legendre symbol (D/N), N odd prime
    r = pow(D % N, (N - 1) // 2, N)
    return 0 if r == 0 else (1 if r == 1 else -1)

def points(p, A, B):
    sq = {}
    for y in range(p): sq.setdefault(y * y % p, []).append(y)
    pts = [None]
    for x in range(p):
        for y in sq.get((x * x * x + A * x + B) % p, []): pts.append((x, y))
    return pts

def add(P, Q, A, p):
    if P is None: return Q
    if Q is None: return P
    if P[0] == Q[0] and (P[1] + Q[1]) % p == 0: return None
    if P == Q: l = (3 * P[0] * P[0] + A) * pow(2 * P[1], -1, p) % p
    else: l = (Q[1] - P[1]) * pow(Q[0] - P[0], -1, p) % p
    x = (l * l - P[0] - Q[0]) % p
    return (x, (l * (P[0] - x) - P[1]) % p)

def mul(k, P, A, p):
    R = None
    while k:
        if k & 1: R = add(R, P, A, p)
        P = add(P, P, A, p); k >>= 1
    return R

fails, cases, curves_checked = [], 0, 0
for p in range(max(P_LO, 5), P_HI + 1):
    if not is_prime(p): continue
    nonres = next(g for g in range(2, p) if pow(g, (p - 1) // 2, p) == p - 1)
    classes = {}
    for j in range(p):
        if j in (0, 1728 % p): continue
        k = (1728 - j) % p
        A, B = 3 * j * k % p, 2 * j * k * k % p
        for (a2, b2) in ((A, B), (A * nonres ** 2 % p, B * nonres ** 3 % p)):
            pts = points(p, a2, b2)
            t = p + 1 - len(pts)
            if t % p == 0: continue  # supersingular
            classes.setdefault(t, []).append((j, a2, b2, pts))
    for t, members in classes.items():
        D0, f = fundamental(t * t - 4 * p)
        if D0 in (-3, -4): continue
        n_E = p + 1 - t
        for N, e in factor(f).items():
            if N == 2 or e != 1 or n_E % N: continue
            cases += 1
            okA = (p - 1) % N == 0 and (t - 2) % N == 0 and n_E % (N * N) == 0
            full = cyc = other = 0
            for (j, a2, b2, pts) in members:
                tors = sum(1 for P in pts if mul(N, P, a2, p) is None)
                curves_checked += 1
                if tors == N * N: full += 1
                elif tors == N: cyc += 1
                else: other += 1
            okC = other == 0 and full > 0 and cyc == (N - kron(D0, N)) * full
            if not (okA and okC):
                fails.append(dict(p=p, t=t, D0=D0, f=f, N=N, full=full, cyc=cyc, other=other, okA=okA))
print(json.dumps(dict(range=[P_LO, P_HI], cases=cases, curves=curves_checked, failures=fails[:20], n_fail=len(fails))))
sys.exit(1 if fails else 0)
