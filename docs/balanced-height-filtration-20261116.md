# Test the whole shift ideal, then change the ideal

16 November 2026. Balanced projective coordinates were a proposed extraction
mechanism. The new test covers arbitrary mixed shifts and cancellations in
the ordinary ideal, then executes a different one-vertex saturation trial.
Ten generic filtration laws and three generic projective-elimination laws
compile, with actual S3 polynomial/prime-field instances. The real weighted-
norm consequence is hand analysis. [pcc:unverified]

The [prospective plan](balanced-height-filtration-20261116-plan.md),
[editable diagram](balanced-height-filtration-20261116/flow.dot),
[PDF](balanced-height-filtration-20261116/report.pdf) and
[publication scope](balanced-height-filtration-20261116/PUBLICATION.md)
separate these proof components from any growing-system root solver.
No LLL run, numerical curve case, native evaluation, benchmark, paid job or
qualification was performed. [pcc:unverified]

## The coordinate change and the row-height correction

Use an S3 path with at least three leaves, so every row touches a projective
intermediate slot. For a short Weierstrass model, write its abscissa as z=U/V
modulo p with V nonzero. The cleared S3(x,y,U/V) row is

    F=(x-y)^2 U^2
      -2((x+y)(xy+a)+2b) U V
      +((xy-a)^2-4b(x+y)) V^2.

The actual prime-field probe checks V^2*S3(x,y,U/V)=F with V!=0, applying
the existing S3 object. Integer polynomial coefficients may be reduced
modulo p; all such choices still belong to the corresponding ordinary shift
ideal. Leaves have integer bound B and projective coordinates have bound H.
The monomial x^2*y^2*V^2 has coefficient1 and weight B^4 H^2. Thus the old
alternatives001 B^2*p number, at H near sqrt(p), is only a selected monomial
lower bound, not the full row norm. The frozen old note is preserved; this
is a separate correction. [pcc:unverified]

For an internal row S3(U/V,x,R/S), clearing V^2*S^2 includes coefficient1
monomials x^2 V^2 R^2 and x^2 U^2 S^2 of weight B^2 H^4. Generic curve/target
coefficients can raise the norm further. No exact whole-row norm is inferred
from one selected monomial, and the new test below needs no such inference.
[pcc:unverified]

## A generic coefficient filtration covers every ordinary shift

Use the existing ring Z[variables]. Assign each projective numerator and
denominator weight1 and each leaf weight0; more generally take ANY additive
nonnegative monomial weight w. Define

    Filter(p,w,t,g) iff p^(t-floor(w(m)/2)) divides coeff_m(g) for all m,

with natural subtraction in the exponent. This predicate is a ring ideal
at each level t. Addition uses common coefficient divisors. For a product,
the inherited coefficient antidiagonal formula and additive weight give

    t+u-floor((d+e)/2)
      <= (t-floor(d/2))_+ + (u-floor(e/2))_+.

Multiplying the two divisibilities and summing proves levelt times levelu
is contained in level(t+u). These are shared polynomial laws, not repeated
arguments for one curve. [pcc:unverified]

The constant p belongs to level1. Every monomial of projective degree at
least2 belongs to level1 with arbitrary integer coefficient. In particular,
ANY quadratic chart A U^2+B U V+C V^2 belongs to level1 when U,V have
weight1, even if A,B,C involve other projective variables. Every cleared
S3 path row has this form. Thus for J=(p,F_1,...,F_s),

    J^t is contained in levelt.

This includes arbitrary polynomial multiples, mixed products, cancellations
and coefficient recentering by multiples of p^t. It assumes the ordinary
ideal of those generators, without saturating out zero projective slots or
adding extra integer identities of smaller projective degree. [pcc:unverified]

For a nonzero coefficient c of projective degree d, put e=(t-floor(d/2))_+.
Its divisibility implies |c|>=p^e for positive p. Since 2e+d>=2t, the
compiled squared coefficient endpoint is

    p^(2t) <= |c|^2 * p^d.

The actual integer S3 chart applies this endpoint to ALL polynomials in
its ordinary shift ideal powers. The shared span-power law supplies the
same endpoint for any family satisfying the generic level1 contract.
No primal/dual lattice was enumerated or numerically reduced. [pcc:unverified]

## Consequence for the balanced HHG certificate

Assume each numerator/denominator bound is H>=sqrt(p) and all leaf bounds
are at least1. Each nonzero weighted coefficient has magnitude at least

    |c| H^d >= |c| p^(d/2) >= p^t.

Therefore every nonzero g in J^t has weighted coefficient norm at least p^t.
The usual sufficient integer-vanishing certificate requires the norm below
p^t/sqrt(number of monomials). It cannot hold for this family, whatever
ordinary mixed shifts or cancellations are chosen. This norm consequence
is hand arithmetic from the compiled coefficient theorem. [pcc:unverified]

The scope matters: this excludes a sufficient HHG certificate in the
specified balanced ordinary-ideal construction. It does not exclude a
saturated ideal, smaller or skew height regions, additional justified
identities, different norm/root techniques, or ECDLP algorithms in general.
No claim about all multivariate Coppersmith methods is made. [pcc:unverified]

## Executed successor: a finite saturation witness

Let two homogeneous quadratic forms at one projective vertex be

    F=aU^2+bUV+cV^2, G=dU^2+eUV+fV^2;
    L=ae-bd, M=af-cd, N=bf-ce, R=M^2-LN.

The generic ring identity checked in ProjectiveQuadratics is

    R V^3 = [a(MV-LU)-LbV] G + [-d(MV-LU)+LeV] F.

It follows from (MV-LU)(aG-dF)-LV(bG-eF). The compiled ideal endpoint
gives R V^3 in any ideal containing F,G; the compiled domain endpoint gives
R=0 at a common root with V!=0. The actual prime-field probe substitutes
two S3 coefficient triples. This is standard quadratic elimination with an
explicit finite denominator witness, not a novelty claim. [pcc:unverified]

For modular lifting, if p does not divide V at the root, divisibility of
V^n*g by p^t implies divisibility of g by p^t. This justifies the different
candidate family

    ((p,F_1,...,F_s)^t : (product V_i)^infinity).

Dividing a denominator witness can leave the old coefficient filtration.
In the one-vertex trial, powers of R give witnesses V^(3t)*R^t in J^t.
Those powers remain dependent equations; no root-recovery independence
claim follows. The finite witness and root consequence are formal; this
general localization/power interpretation is hand algebra. [pcc:unverified]

## A concrete next solver obligation

Construct bounded saturation witnesses first, then use Ryan's optimal shift
selection for a specified ideal and finite monomial set. Charge every
denominator exponent, multiplicity, coefficient bit height, monomial count,
ideal calculation, lattice rank and candidate branch. Keep a hard total cap,
return failure if it is exceeded, and preserve original support/provenance.
Nonzero denominators must be enforced; infinity and coincident-chart cases
need their own complete treatment. [pcc:unverified]

For homogeneous short equations, recover ratios on the projective quotient;
the affine cone retains a scaling dimension for every projective slot.
Setting V=1 for rational root recovery AFTER a homogeneous integer identity
has been established differs from assuming the bounded integer root had
denominator1 before the lattice step. Root finiteness on that quotient still
needs proof, and every actual point/sign and primitive coefficient must be
checked at the end. [pcc:unverified]

Direct sequential elimination has a cost warning: eliminating a quadratic
against a neighboring quadratic produces a quartic in the next projective
slot; repeated degrees can double. A small local map degree alone does not
bound the total frontier. The next discriminating calculation is whether
bounded-width saturation plus genuinely short independent equations avoids
that growth while retaining useful original relations. This step is not
implemented or assumed. [pcc:unverified]

## Primary source and audit boundary

Ryan2025, author's UCSD thesis chapter3 (full EUROCRYPT2025 reprint), printed
pp55--68: HHG lemma6; zero-dimensional heuristic3; ideal powers; Algorithm5
and theorem3 optimality for a FIXED ideal and monomial set. The primary
source supports a different ideal-selection trial, not a proof that the
resulting equations are independent or cheap when dimension grows. Direct
eprint and Jochemsz--May PDF access failures are preserved; no theorem was
imported from an unread abstract. Sources checked (KB): unavailable; exact
pinned Mathlib/owner search and accessible primary fallback are indexed.
No generic impossibility or novelty claim. [pcc:unverified]

Canonical gate001 exits0 with271 audited theorems,0 failing and0 trusted-
native exceptions. All thirteen new actual named axiom prints use only
allowed standard axioms. Records and actual instances are in the canonical
publication index, with all raw failed floor/source diagnostics retained. No sorry,
custom axiom, native_decide, proof-limit, trust, inventory or linter policy
exception. All earlier91 frozen subjects remain intact. No evaluated native
identity certificate, numerical case, paid or qualification execution.
The complete original algorithm criterion remains unmet. [pcc:unverified]
