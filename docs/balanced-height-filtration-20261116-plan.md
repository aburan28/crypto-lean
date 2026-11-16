# Balanced projective heights: test the entire ordinary shift ideal

16 November 2026. Prospective mathematical/compiler work. Existing universal
pool PR25 is open; finished successor work extends it without changing any
of the91 frozen subjects or ten old ledger rows. No numerical crypto cases,
LLL, benchmarks, native evaluations, qualification or paid jobs.

## Question and prediction

Do balanced rational intermediate coordinates actually allow the ordinary
Coppersmith shift ideal to cross the integer-vanishing threshold? Prediction:
no, for a precise unsaturated family. If every modular input has projective
degree at least2, every polynomial g in J^t, J=(p,F_1,...,F_s), has

    p^(t-floor(d/2)) dividing each coefficient of projective degree d<2t.

At balanced coordinate bound H>=sqrt(p), any nonzero coefficient then has

    |c|^2 p^d >= p^(2t).

Thus its weighted magnitude is at least p^t, already too large for the HHG
sufficient test. This is a filtration statement about the ENTIRE ordinary
ideal, including mixed powers and cancellations, not only the initial rows.
It is not a theorem excluding saturated ideals, smaller height regions,
other coordinate systems or other algorithms.

The mechanism to test next is saturation BEFORE optimal shift selection:
J_t=((p,F_1,...,F_s)^t : (product V_i)^infinity), with nonzero denominators.
If a saturation witness has V^n*g in the old ideal, gcd(V(root),p)=1 lets
one cancel V(root)^n modulo p^t. But the old coefficient filtration need
not survive that division. This is an explicit mathematical difference,
not a proposal to repeat unchanged LLL with more shifts. Mixed projective
blocks and rational/projective root recovery still need a total rank,
degree, success and provenance cap.

## Sources and correction to preserve

KB MCP unavailable; bounded pinned Mathlib and primary fallback. Keegan Ryan,
Practical Lattice-based Algorithms for Cryptanalysis (UCSD2025), chapter3
is the author's full EUROCRYPT2025 reprint of Solving Multivariate
Coppersmith Problems with Known Moduli. Read printed pp55--68: HHG lemma6,
zero-dimensional heuristic3, shift ideal J_k, Algorithm5 and theorem3.
Optimality is relative to an ideal and a monomial set, not a proof of zero-
dimensional root recovery or a uniform bound when variable count grows.
Primary thesis https://escholarship.org/uc/item/8bz3g5b6 and
https://escholarship.org/content/qt8bz3g5b6/qt8bz3g5b6.pdf.
Direct eprint and Jochemsz--May author/archive PDFs returned403; retained
access receipts. Ryan's primary review supplies the required assumptions.
No novelty claim or generic multivariate impossibility inference.

Preserve old alternatives001 byte-for-byte. Its B^2*p end-row number is a
selected monomial lower bound, not the complete norm. In the homogenized
S3(x1,x2,U/V) row, x1^2*x2^2*V^2 has coefficient1 and weight B^4*H^2.
An internal S3(U/V,x,R/S) row also has coefficient1 monomials of weight
B^2*H^4. Generic field coefficients can increase these weights further.
The present test does not rely on a claimed exact full-row norm.

## Six fields before the new Lean family

1. Structure: MvPolynomial sigma Z, additive monomial weights
   w:(sigma ->0 Nat)->+Nat, integer divisibility, ring ideals and ideal powers.
2. Existing laws: MvPolynomial.coeff_add/coeff_mul/coeff_monomial;
   finite antidiagonal sum and Finset.dvd_sum; dvd_add/dvd_mul, pow_add,
   pow_dvd_pow; Ideal.span_le/mul_le/pow_succ; Nat.le_of_dvd,
   Int.natAbs_dvd_natAbs and monotonicity of natural powers.
3. Object: the existing polynomial ring, not new syntax. A predicate on
   coefficients defines a generic ideal. Actual projective S3 chart rows
   are quadratic forms A U^2+B U V+C V^2 in this same ring.
4. Floor: compile coefficient-convolution/ideal/divisibility interfaces
   first, before defining the new filter. Then actual polynomial chart
   rows and prime-field rational S3 identity apply unchanged owner laws.
5. Missing only: closure of the coefficient filter under sum/product;
   resulting ideal power inclusion; generic low-support/monomial/chart
   memberships and a squared coefficient-size consequence. Shared owner
   CryptoLean.Polynomial.BalancedFiltration owns all generic laws.
6. Inheritance table:

| Operation | Inherited law | New glue |
|---|---|---|
| Sum coefficients | coeff_add, dvd_add | coefficient filter addition |
| Multiply coefficients | coeff_mul, antidiagonal, dvd_sum | filtration convolution |
| Arbitrary polynomial multiples | level0 and product closure | ideal structure |
| All mixed shifts | Ideal.mul_le, pow_succ | power inclusion |
| Actual chart generators | coeff_monomial, quadratic form | generic membership |
| Integer coefficient size | natAbs divisibility, le_of_dvd | squared inequality |
| Real weighted norm/HHG failure | existing HHG lemma6 | hand consequence only |

## Proof chain and controls

Set Filter(p,w,t,f) iff for every exponent m,
p^(t-w(m)/2) divides coeff_m(f), with natural subtraction. Addition uses
one common divisor. For multiplication, coeff_m(fg) is an antidiagonal
sum. For m=a+b, w(m)=w(a)+w(b), and

    t+u-floor((w(a)+w(b))/2)
      <= (t-floor(w(a)/2))_+ + (u-floor(w(b)/2))_+.

Multiply the two divisibilities, weaken the exponent and sum. Level0 is
all polynomials. Therefore each level is an ideal and levelt times levelu
lies in level(t+u). Span generators in level1 give J^t subset levelt.
For c!=0, p^e divides c gives |c|>=p^e, and 2e+d>=2t gives the squared
bound. No real transcendental inequality is disguised as a formal result.

Controls: t=0, weight0 leaf variables, odd degree, degree>=2t, p=1,
zero polynomial/coefficient excluded only where required, arbitrary mixed
shifts and cancellations, empty generator set, saturation explicitly outside
the statement, H smaller than sqrt(p) explicitly outside the norm corollary.
One Lake process at a time, raw failures retained, no trust/limit/linter/
inventory changes. Canonical audit plus actual named axiom prints before
publication. Do not modify old hypotheses or signed/unsigned claim records.
