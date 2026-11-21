"""Exact brute-force check of CryptoLean.ConductorGap(+Bridges) on small prime fields.

Usage:  python3 check_gap.py [P_LO P_HI]      (default 5 1500, as reported)

For every prime p in [P_LO, P_HI], every ordinary F_p-isogeny class with trace t
(t^2 - 4p = d_K f^2, d_K fundamental, d_K not in {-3, -4}) and every odd prime
N with h = v_N(f) >= 1 and N | #E = p + 1 - t, count #E(F_p)[N] by brute force
on every curve of the class (one model per j-invariant = one F_p-isomorphism
class of trace t, since t != 0).

  (A) Theorem 3.4 (gap_prime_dvd_order): N | p-1, N | t-2, N^2 | #E.
  (S) sanity (not a prediction: forced by N | #E and E[N] = (Z/N)^2):
      #E(F_p)[N] in {N, N^2}.
  (C) Theorem 3.2 + F8 + class-number formula, for any height h: the curves with
      full rational N-torsion are exactly those above the floor, so
        #cyclic * (1 + (N - chi)(N^(h-1) - 1)/(N - 1)) == #full * N^(h-1) (N - chi),
      chi = (d_K / N).  For h = 1: #cyclic == (N - chi) * #full.
  (NC) negative control: the wrong relation #cyclic == N^h * #full must fail on
      classes with chi != 0 (reported, not a failure of the check).

Classes with N not dividing #E have t != 2 (mod N) and no rational N-torsion; the
t = -2 (twist) branch of Theorem 3.2 is the class of trace -t, enumerated too.
Not tested here: Theorems 2.3 and 4.3, and levels computed independently of
torsion. No randomness. Prints one JSON line; exit 1 on any failure.
"""
import json, sys
P_LO, P_HI = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (5, 1500)

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

def main():
    fails, pairs, classes_seen, curve_checks, by_h = [], 0, set(), 0, {}
    nc_tested = nc_failed = 0
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
                if t % p == 0: continue  # supersingular (p >= 5)
                classes.setdefault(t, []).append((j, a2, b2, pts))
        for t, members in classes.items():
            D0, f = fundamental(t * t - 4 * p)
            if D0 in (-3, -4): continue
            n_E = p + 1 - t
            for N, h in factor(f).items():
                if N == 2 or n_E % N: continue
                pairs += 1; classes_seen.add((p, t)); by_h[h] = by_h.get(h, 0) + 1
                okA = (p - 1) % N == 0 and (t - 2) % N == 0 and n_E % (N * N) == 0
                full = cyc = other = 0
                for (j, a2, b2, pts) in members:
                    tors = sum(1 for P in pts if mul(N, P, a2, p) is None)
                    curve_checks += 1
                    if tors == N * N: full += 1
                    elif tors == N: cyc += 1
                    else: other += 1
                chi = kron(D0, N)
                lhs = cyc * ((N - 1) + (N - chi) * (N ** (h - 1) - 1))
                rhs = full * N ** (h - 1) * (N - chi) * (N - 1)
                okC = other == 0 and full > 0 and lhs == rhs
                if chi != 0:
                    nc_tested += 1
                    if cyc != N ** h * full: nc_failed += 1
                if not (okA and okC):
                    fails.append(dict(p=p, t=t, D0=D0, f=f, N=N, h=h, full=full, cyc=cyc,
                                      other=other, okA=okA))
    print(json.dumps(dict(range=[P_LO, P_HI], class_N_pairs=pairs, classes=len(classes_seen),
                          pairs_by_height=by_h, curve_checks=curve_checks,
                          negative_control=dict(tested=nc_tested, failed=nc_failed),
                          failures=fails[:20], n_fail=len(fails))))
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main())
