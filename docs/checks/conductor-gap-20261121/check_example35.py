"""Example 3.5 / Proposition 3.4 of the manuscript: p = 1531, t = -43.

Brute-force group structure of E(F_p) for the crater curve j = 182 and the
floor curve j = 51 (models y^2 = x^3 + A x + B as below), compared with
Proposition 3.4: E(F_p) = Z/g x Z/(#E/g), g = gcd(x - 1, f/c), where
d_K = -19 (omega^2 = omega - 5), f = 15, pi = x0 + 15 omega, x0 = -29.
"""
import sys
from math import gcd, lcm
from check_gap import points, mul, factor, fundamental

p, t_expected = 1531, -43
x0, f = -29, 15
assert fundamental(t_expected ** 2 - 4 * p) == (-19, f)
assert 2 * x0 + 1 * f == t_expected          # tr(x0 + f omega) = 2 x0 + b f, b = 1

def structure(A, B):
    pts = points(p, A, B); n = len(pts); e = 1
    for P in pts:
        o = n
        for q in factor(n):
            while o % q == 0 and mul(o // q, P, A, p) is None: o //= q
        e = lcm(e, o)
    return p + 1 - n, (n // e, e)

ok = True
for name, (A, B), c in (("crater j=182", (535, 757), 1), ("floor j=51", (554, 165), 15)):
    t, (m1, m2) = structure(A, B)
    e = f // c
    g = gcd(x0 - 1, e)            # pi = x0 + e * (c omega) in O_c
    pred = (g, (p + 1 - t) // g)
    print(f"{name}: t={t} E(F_p)=Z/{m1} x Z/{m2}  predicted Z/{pred[0]} x Z/{pred[1]}")
    ok &= (t == t_expected and (m1, m2) == pred)
print("PASS" if ok else "FAIL"); sys.exit(0 if ok else 1)
