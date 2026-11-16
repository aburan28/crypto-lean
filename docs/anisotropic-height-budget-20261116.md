# Concentrated height shrink and matched modulus rows

16 November2026. Source1a140f8 adds fifteen generic laws and eight semantic
checks. They compile locally with standard axiom dependencies; the canonical
all-tracked audit is recorded separately in PUBLICATION. No numerical, Sage,
curve, LLL, paid or qualification run occurred. The complete classical
subexponential prime-field ECDLP objective remains unmet. [pcc:unverified]

The new candidate concentrates rational-height shrink on one/few internal
coordinates and pairs it with a sparse modulus-monomial menu. This avoids a
proved leaf-support obstruction without claiming short equations exist.
The [plan](anisotropic-height-budget-20261116-plan.md),
[diagram](anisotropic-height-budget-20261116/flow.svg),
[PDF](anisotropic-height-budget-20261116/report.pdf) and
[publication scope](anisotropic-height-budget-20261116/PUBLICATION.md)
retain the assumptions and unresolved obligations. Earlier pinned source,
plans, claims and reports remain unchanged. [pcc:unverified]

## The exact leaf-support test

Reuse the existing ordinary-ideal filtration. For projective degree d, every
coefficient c of a member of (p,F1,...,Fs)^t satisfies

    p^(t-floor(d/2)) divides c, with natural subtraction.

For H>=1 and H²<=p, a nonzero coefficient consequently obeys

    H^(2t) <= |c| H^d.

Indeed |c|>=p^e>=H^(2e), e=max(t-floor(d/2),0), and 2e+d>=2t.
This exact integer statement is compiled. If a monomial has positive leaf
degree and leaf bound B>=1, its weighted coefficient is at least B H^(2t).
The whole L1 norm is at least any one coefficient. Therefore

    L1 < p^t and B H^(2t)>=p^t  =>  every leaf coefficient is zero.

The generic theorem accepts an actual weight lower bound. Its product-height
law transfers to unequal per-slot heights, taking H as their minimum. The
formal result also applies to arbitrary polynomial multiples and cancellations
in the declared ordinary ideal power. It is not a saturation theorem.
[pcc:unverified]

An actual translated four-leaf S3 path is checked against the owners, with
two projective slots, per-slot weights and original ideal powers. A generic
shifted-quadratic law verifies coordinate translation without a new curve
proof. Prime-field denominator clearing and cyclic S3 symmetry are separate
semantic checks. These are compiler proofs, not curve experiments.
[pcc:unverified]

## Why unequal heights can change the budget

Write H_i=sqrt(p)/L_i, L_i>=2, and s=m-2. The preceding report's positive
primitive rational pairs have at least H_i²/4 distinct residues. Thus fixed
tuple coverage under independent uniform offsets is at least
product_i(1/(4L_i²)). A simultaneous pool of

    N >= ceil(product_i(4L_i²) * (s ln p+ln(1/epsilon)))

covers all finite tuples with probability at least1-epsilon. Conversely,
signed bounded fractions normalize to positive denominator and occupy at
most2H_i²+1<=3H_i² residues. Any universal signed-box pool needs

    N >= product_i(L_i²/3).

For L_i>=2, log(L_i²/3)>=(2-log(3)/log(2))*log L_i. Hence fixed-error
universal coverage is subexponential exactly when sum_i log L_i=o(log p).
These rational counting/probability applications are hand analysis, not new
compiled theorems. Infinity cases and restricted promise sets are separate.
[pcc:unverified]

Uniform H=sqrt(p)/L must satisfy L^(2t)>B before an ordinary HHG-short row
can contain a leaf. If t is fixed, m grows, m=o(log p) and B^m is approximately
p on the logarithmic scale, the signed universal-cover lower bound then gives
N>=p^(1/t-o(1)). Uniform fixed-multiplicity eligibility costs too much for
this strategy. This is not an ECDLP lower bound. [pcc:unverified]

Instead take one L_i=B^kappa, kappa>1/(2t), and all other L_i=2. The support
threshold no longer excludes leaf dependence, while sufficient pool cost is
B^(2kappa)*exp(O(m)) times the logarithmic universe factor. It stays
subexponential when log B=o(log p) and m=o(log p). Integer floors only add
constant factors per coordinate once heights remain positive. Eligibility
is not a useful equation or yield guarantee. [pcc:unverified]

A fair comparison fixes the SAME total dyadic shrink K. Uniform allocation
spreads k_i approximately K/s; concentrated allocation spends most of K at
one slot. For fixed t and suitable growing K, the first profile is excluded
by the leaf-support test while the second is eligible, with the same
worst-case coverage lower bound and counted chart budget. This is a
mathematical eligibility separation, not a measured performance difference.
[pcc:unverified]

A frozen dyadic grid can spend this budget without postselection. Let k_i>=1,
sum k_i<=K and H_i=floor(sqrt(p)/2^k_i)>=1. There are at most choose(K,s)
profiles. Each retains a fixed tuple with probability at least2^(-2K-4s).
One shared offset pool of size

    ceil(2^(2K+4s) * (s ln p+ln(choose(K,s))+ln(1/epsilon)))

simultaneously covers every tuple/profile pair. Both profile enumeration and
pool size are subexponential if K=o(log p), since s<=K and choose(K,s)<=2^K.
That event allows adaptive profile selection from the frozen grid. All solver
trials still count; the source prototype does not implement this successor.
[pcc:unverified]

## Small degree blocks do not supply independence

For the ordinary S3 chain, generator powers e_0,...,e_(m-2) give projective
multidegree2(e_j+e_(j+1)) at slot j. Its head e_0 and all adjacent sums
uniquely determine the power vector, by successive cancellation. With
sum(e)<=t, a fixed profile therefore has at most t+1 power records.
A finite shift menu M gives at most(t+1)|M| records in one shifted profile.
These finite injection/cardinality laws are compiled, and an actual ordinary
variable-layout check uses them. Records are indexed by power vector and
shift; duplicate polynomial values do not erase record multiplicities.
[pcc:unverified]

This controls row rank per block, not the number of columns, determinant,
LLL approximation loss or number of blocks. The semantic multihomogeneity
connection is hand accounting plus the S3 checks; arbitrary saturation
families need their own profile bound. Classical LLL loses an exponential
factor in rank. That factor and the L1 conversion must be charged against
an actual determinant margin; no positive margin is established here.
Ryan2025 printed pp5--6 and chapter3 provide the primary context.
[pcc:unverified]

There is also a support-separation catch. Let I be the chosen integer-lift
ideal; every generator has projective degree at least2. Pure p^t monomial
shifts of total degree0/1 occupy only projective weights0/1. Write a linear
combination as f=a+p^t b, with a in I and b supported in those low weights.
Any nonzero low coefficient of f has magnitude at least p^t. At scales>=1
it cannot survive L1<p^t. Thus b=0 and f remains in I. This modulus-part
test and its original-ideal consequence are compiled. [pcc:unverified]

It does NOT prove arbitrary extraction impossible. If I is proper and has a
nonempty positive-dimensional leaf projection, a subideal of I cannot give
finite nonempty leaf projection. That extra premise has not been proved for
arbitrary independently centered lifts. Their characteristic-zero ideal must
not be replaced silently by the exact S3 curve ideal. Saturation, other lift
choices and higher matched modulus rows are outside this support-gap test.
[pcc:unverified]

## A concrete successor family, with the missing step exposed

Use a frozen concentrated/dyadic height profile and offset panel. For the
ordinary translated lifts, let M contain1 and every monomial in each original
row's support. S3 has constant local support, so |M|=O(m), with degrees<=6.
This sparse menu puts p^t rows on the original coefficient columns and avoids
the degree0/1 separation. It is not Ryan's optimal D-Groebner selector.
[pcc:unverified]

At fixed t, full power/shift records number at most
choose(m-1+t,t)*|M|, with each block at most(t+1)|M|. Polynomial total degree
is at most6t+6 in3m-4 variables, so the dense column count is bounded by
choose(3m-4+6t+6,6t+6). These are prospective finite-family bounds. Actual
rank, determinant and bit heights must be retained; sparse supports do not
justify dropping raw rows or zero/failure records. [pcc:unverified]

The smallest informative future comparison would hold catalog, target,
labels, t, matched menu and counted resources fixed, and compare uniform
against concentrated height. Record short rows, leaf support, finite leaf
projection, original signed decomposition and separate scalar replay as
different outcomes. No trial is launched here, and the older pinned scalar-
height/degree0/1 prototype is not silently modified. [pcc:unverified]

Still missing: a proved positive determinant/minima margin that beats LLL
loss; independent useful equations across the whole chain; finite root cost;
useful original random-target yield; and complete cold scalar-recovery cost.
An admitted toy could falsify mechanics, not prove asymptotics. The source
and proof results here do not meet the original completion criterion.
[pcc:unverified]
