# Distinct-generator b cancellation: exact algebra, expensive universal coverage

16 November2026. Twenty generic owner laws and five semantic declarations compile.
This tests a genuinely different modular family from multiples of one S3 generator;
it is not a numerical trial or complete ECDLP algorithm. Full end-to-end classical
subexponential prime-field ECDLP criterion remains unmet. [pcc:unverified]

## What changed

The preceding [single-generator analysis](curve-first-selector-20261116.md)
exposed a generic-model bottleneck from a shared irreducible S3 factor. Here two
distinct actual generators give a polynomial that is independent of b. The
algebra is valid, but the primitive projective profile makes the universal-chart
version too expensive. Adaptive useful-solution coverage, factor-aware variants
and other certificate families are not settled by this test. [pcc:unverified]

## Exact cancellation and preservation

For A=x+y+z, B=xy+xz+yz and C=xyz, actual S3 equals

    F=(B-a)^2-4A(C+b).

The compiled generic cleared form uses

    Fi=(Bi-aDi)^2-4Ai(Ci+bDi), Zi=AiDi;
    G=Z2F1-Z1F2
     =A2D2(B1-aD1)^2-A1D1(B2-aD2)^2
       -4A1A2(D2C1-D1C2).

Thus b cancels exactly, without assuming equal sums, denominators or offsets.
Both generators must be genuine equations of the SAME original decomposition.
Retain F1: on Z1!=0, F1=G=0 is equivalent to F1=F2=0. On Z1=0 retain the
original pair as an explicit separate branch. This branch has no free recovery
algorithm; its cost must still be charged. All these ring/field identities and
the zero-branch decomposition compile. [pcc:unverified]

## Strip the forced shared denominator before estimating cost

Take adjacent triples (x,y,Z/V) and (Z/V,w,T/W), with x,y,w bounded leaves.
Their actual cleared S3 equations are

    F1=(x-y)^2 Z²-2((x+y)(xy+a)+2b)ZV
                  +((xy-a)^2-4b(x+y))V²;
    F2=(Z-wV)^2 T²-2((Z+wV)(Zw+aV)+2bV²)TW
                  +((Zw-aV)^2-4b(Z+wV)V)W².

Let A1=Z+(x+y)V and A2=ZW+wVW+TV. Their denominator products are D1=V,
D2=VW. The naive expression is V times

    G0=A2*W*F1-A1*F2.

The compiled primitive identity is

    G0=A2W(B1-aV)^2-A1(B2-aVW)^2-4A1A2(WC1-C2).

G0 is b-free and still has a DIRECT original-ideal witness. Its vanishing
follows from F1=F2=0 even on V=0; this implication does not divide by V. To
recover F2 from F1,G0 use A1!=0 and retain the A1=0 original-system branch.
Separately, the affine S3 interpretations require V,W nonzero; infinity cases
remain original projective equations, never discarded. [pcc:unverified]

The primitive expression has profile(3,2) in (Z,V),(T,W), not the naive(4,2).
The compiled scaling identity is

    G0(rZ,rV,sT,sW)=r³s²G0(Z,V,T,W).

The substitutions Z=U+tau V,T=X+sigma W preserve those grades. Generic
specializations also compile:

    G0|V=0 = Z³((x-y)^2W²-(T-wW)^2);
    G0|W=0 = -(Z+(x+y)V)(Z-wV)^2T².

Explicit guarded nonzero semantic declarations show that neither denominator
variable divides the generic expression. This checks forced denominator factors;
it is not a complete factorization of every finite-field specialization. A
factor-aware branch search would be a different obligation. [pcc:unverified]

## Ordinary norm and universal-cover cost

For every nonzero polynomial supported on this fixed profile, with positive leaf
weights and projective heights H1,H2>=1, every nonzero monomial has weight at least
H1³H2². Hence weighted L1>=H1³H2². Centering coefficients or adding p rows on
the SAME support does not change that profile. The compiled min-support-weight
law states the exact nonzero-polynomial premise; the application transfers the
displayed homogeneous profile to that weight premise. [pcc:unverified]

A certificate under the ordinary modulus-p bound L1<p therefore requires

    H1³H2² < p, hence K=H1²H2² < p.

Each signed rational box, with |U|<=H and 1<=V<=H, has at most3H² residues.
One two-chart translate consequently covers at most9K internal-coordinate pairs.
A universal collection of Q such translates covering all Fp² must satisfy

    p² <= 9QK, and therefore p < 9Q.

The finite-union cardinal bound, profile-product inequality, resulting arithmetic
charge and a combined semantic application compile. The per-chart3H² bound is
the elementary hand signed-box count reused from the previous reports. The
constant9 is inessential: universal coverage requires linear cost in p.
[pcc:unverified]

At heights p^(1/2-o(1)) in both slots, H1³H2²=p^(5/2-o(1)) already exceeds p.
Shrinking the heights sufficiently makes universal two-coordinate coverage cost
at least p/9. Thus this ordinary norm-certificate PLUS universal-chart strategy
does not provide a subexponential selector. This conclusion does not reject
adaptive coefficient-selected charts, nonuniform useful decompositions,
factor-aware certificates, saturation, different norms or all ECDLP methods.
[pcc:unverified]

## A sharper HAND adaptive test: three coefficient anchors

Assume p>3 prime, B>=2 and H1,H2>=1, fixed independently of b. The
universal-cover failure is not the only discriminator. For
Z=U+tau V,T=X+sigma W, the displayed G0 has the following coefficients:

    x²y²w V³W² : 1,
    x²yw  V³W² : -2tau,
    x²y²  V³W² : tau+sigma.

These are HAND extractions from the leaf-degree5 and4 parts, not new compiled
coefficient theorems. At degree4 the subtraction A1F2 contributes nothing;
the relevant terms of A2WF1 are

    x²y²(ZV²W²+TV³W)-2wxy(x+y)ZV²W².

Thus a rank-one row family pZ^N+ZG0(tau,sigma), with full matching-profile
modulus rows, admits a three-coefficient existence search. Enumerate a nonzero
small lambda and two small integers c,d, then set

    tau=-c/(2lambda), sigma=d/lambda-tau.

Center ALL coefficients and retain an exact full-row witness/norm test. The
same positive-weight/centering argument as before gives a complete HAND search
for this declared row family, not arbitrary distinct-generator spans. With
L=H1³H2², the cutoffs are n0=floor((p-1)/(B^5 L)) and
n1=floor((p-1)/(B^4 L)); there are at most2n0(2n1+1)² raw records. All candidates
depend on p,a,B,heights but NOT b. If the cutoffs are p^o(1), the entire eligible
offset-pair image has size S=p^o(1), even when an algorithm chooses its subset
after seeing b. This is not a tested implementation or a new Lean equivalence.
[pcc:unverified]

For each such first chart, at most3H1² rational residues and (2B+1)² bounded
leaf pairs (x,y) occur. On A1!=0, the first ORIGINAL S3 equation determines a
unique b from those three abscissas. Therefore, for fixed a, the number of b
values admitting ANY original nonzero-pivot decomposition inside these charts
is at most

    S * 3H1² * (2B+1)².

Shortness requires H1³H2²<p, hence H1²<p^(2/3) when H2>=1. For B,S=p^o(1),
the fraction among uniform b is at most p^(-1/3+o(1)) on THIS branch. Restricting
to nonsingular b changes only a bounded number of excluded values. This bounds
a whole b-independent compatible-chart image, not an unjustified fixed pool
chosen after seeing b. [pcc:unverified]

The exceptional branch is essential: A1=0 and F1=0 give z=-(x+y) and
a=-(x²+xy+y²). Then the first equation imposes no condition on b, and G0 adds
no replacement for F2 at that branch. It cannot be dropped or included in the
preceding b count. The complete original second equation and its recovery cost
remain. No useful-yield or independent-equation conclusion for this exceptional
branch is asserted. [pcc:unverified]

## Evidence and next discriminator

Owner CryptoLean.Polynomial.CurveParameterElimination has20 named generic laws,
all actual named axiom prints standard. Five semantic declarations compile:
translated original-root preservation; the actual retained-equation branch;
two guarded denominator nonfactor witnesses; and universal two-chart cost under
the declared profile/coverage premises. No new scientific arithmetic, curve/LLL,
native qualification, paid or numerical run. Raw failures remain. [pcc:unverified]

This attempt removes a parameter without losing the original equations, but its
universal-cover cost fails. The three-anchor adaptive test then limits generic
b yield on the nonzero-pivot branch. Next check those exact coefficient anchors
against the source and analyze the EXCEPTIONAL branch's retained F2 cost and
useful equation independence. A higher-rank distinct-generator span is outside
this rank-one G0 count. Known prefix sums can be precomputed, but fixing a prefix
and substituting F1=0 makes G0=-A1F2; that alone returns to a one-generator
endpoint family. No useful-yield claim.
[pcc:unverified]

Before another driver, require a precise selected-chart family, complete original
point/sign/denominator provenance, all prefix/precomputation costs, and a genuine
intersection/yield proof or an admitted falsification experiment. The prior
unknown live budget/runtime/image/caller/capacity/custody prerequisites still
prevent any numerical trial here. Source/proof work uses the existing development
boundary. No paid retry or expanded admission is implied. [pcc:unverified]
