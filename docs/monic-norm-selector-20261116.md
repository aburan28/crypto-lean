# Monic tight norms and an actual-input obstruction to cubic-residue filtering

This phase tests a normalization of tight interpolation rows and a stronger
discriminator for the previously rejected cubic-residue shortcut. It supplies
complete supplied-row postprocessing and an actual odd-subgroup obstruction;
fast discovery of the nonzero row and the complete classical subexponential
prime-field ECDLP algorithm remain open. [pcc:unverified]

## Complete normal form for a supplied tight row

Use the actual source cubic f=X^3+aX+b and N=u^2-f*v^2. For a nonzero pair,
the leading terms cannot tie: their degrees are2deg(u) and3+2deg(v).
The source now classifies the leading degree and coefficient, including
zero-component boundaries. For a tight norm on t distinct selected x's:

- Even branch: t=2deg(u), LC(N)=LC(u)^2, u!=0.
- Odd branch: t=3+2deg(v), LC(N)=-LC(v)^2, v!=0.

Divide BOTH u and v by the nonzero leading coefficient of the dominant
polynomial. Actual norm scaling, row-zero equivalence, preservation of both
degrees and explicit recovery are formal. The dominant component becomes
monic, and every tight solution becomes N=nodal in the even branch or
N=-nodal in the odd branch. This uses field inversion of a supplied nonzero
coefficient, with no square-root or discrete-log oracle. [pcc:unverified]

The usual pole-budget basis has t coefficients for t>=3. This normal form
removes its arbitrary scalar parameter, leaving a hand t-1 parameter count.
That is a representation reduction, not a reduction of b^t colored-choice
enumeration or a measured/runtime search bound. [pcc:unverified]

## Exact supplied-row colored extraction

For actual curve records with globally injective x coordinates, the maintained
color product is a product of actual evaluation factors within one color.
Its vanishing means at least one factor vanishes. A nonzero row of norm
degree at most the number of colors therefore gives at least that many
distinct norm roots. The tight signed zero-locus law leaves exactly one
zero factor per color. [pcc:unverified]

The new owner source formalizes the unique colored choice and actual finite
zeroChoices filters: every filter is a singleton, and normalization preserves
it exactly. The uniqueness is for a FIXED supplied pair, not uniqueness of
all solutions on the same pool. The finite filter can be scanned once a row
is known; hand evaluation accounting is polynomial in pool size and degrees.
No efficient nonzero-row discovery bound follows. [pcc:unverified]

Controls retain zero-u/odd norms, empty nonzero constants and the empty colored
choice. The zero pair keeps all factors and is explicitly excluded from the
uniqueness theorem. Characteristic2 coalesces the two norm signs but not the
degree parity; the actual point residue results below explicitly require
characteristic other than2. Earlier duplicate-x and zero-input branches are
not removed from the full research problem. [pcc:unverified]

## Why the cubic-square shortcut cannot prune odd-subgroup tuples

The earlier symbolic false positive did not by itself establish behavior on
the original elliptic input regime. The new source supplies that connection
using Mathlib's actual affine Point, Equation, slope, addX and xRep semantics.
[pcc:unverified]

For a finite short-curve point R=(r,s), s!=0, let m be the tangent slope and
xP=m^2-2r the doubled abscissa. Define the actual quadratic polynomial

    H(X)=m-(X^2+rX+r^2+a)/s.

The checked identity is

    H(X)^2-(xP-X)=f(X)*(X+2r)/s^2.

First the cleared and unit-inverse versions are formal over a commutative
ring, then the actual polynomial identity and divisibility over a field.
This matches the actual Mathlib point addition coordinates. [pcc:unverified]

If q is odd and qP=0, the public point [(q/2)+1]P doubles to P. For P!=0
its half is finite and has nonzero ordinate; infinity and zero-ordinate cases
are handled explicitly in the proof. No unknown ECDLP scalar is used. The
half equality is formal; the usual O(log q) double-and-add accounting is HAND.
[pcc:unverified]

Consequently, for EVERY selected tuple of nonzero points killed by one odd q,

    f divides U^2-product_i(C x_i-X)

has a witness U of degree at most2. Products retain index multiplicities and
allow arbitrary point correlations; distinct x's are unnecessary for this
obstruction. The reduction to degree2 uses actual polynomial remainder by the
monic cubic. The final symbolic application covers mixed point pools
alpha_p*G+beta_p*H with qG=qH=0, the original ECDLP input form. [pcc:unverified]

The target product equals (-1)^t times the monic nodal polynomial, so this
is also the sign appearing in the normalized norm congruence. That elementary
product-sign identification is written here, not an additional compiled law.
Thus the BARE cubic-square test accepts every tuple in the stated regime.
For an ambient u cap at least2, the bounded residue witness fits that cap.
Extra monicity and the FULL polynomial-square quotient remain separate;
no claim says that every tuple passes those stronger conditions. [pcc:unverified]

In particular this rejects the proposed residue condition as a pruning step
on these odd-subgroup inputs. It does not reject complete norm solving,
degree-restricted reconstruction or all selectors. Identity records are an
explicit separate recovery/label branch; the nonzero-record hypothesis is
not a claim about every original sample. [pcc:unverified]

## Remaining algorithmic obligations

The central task remains finding a nonzero tight normalized row with its
FULL polynomial-square quotient and selected signs, at controlled cost and
useful yield on the original input law. A polynomial norm solution alone can
encode a different sign choice; all original selected-row checks remain.
The principal-divisor/pole/actual group-ZERO-SUM bridge from tight interpolation
functions remains HAND; the new formal group-DOUBLING residue bridge must not
be mistaken for it. The mixed-label recovery denominator is another checked
condition in the subgroup scalar field, not the curve base field.
[pcc:unverified]

A next discriminating idea is to test higher f-adic congruences versus
degree-restricted reconstruction. Hypothesis only: unit square roots may lift
to every finite f-adic precision, leaving unconstrained congruence tests
uninformative; a tight-degree or Padé condition would have to carry the useful
restriction. No such lifting/search theorem or numerical test is claimed in
this phase. No full subexponential algorithm or measured speed is established.
[pcc:unverified]

## Validation and preservation

Two new maintained modules contain29 generic laws (15+14) and7 symbolic
applications (6 monic/control+1 actual mixed group). Final owner builds,
actual002,mixed002 and axioms001 exit0; both application logs are empty.
Twenty-nine named axiom probes use standard dependencies. Canonical all-tracked
gate001 exits0:635/0/0. Its38 additions from597 are29 owner laws,7 symbolic
applications and2 generated defining equations, with no removals. Final
source11ce031 predates the audit and is unchanged throughout it.
No proof-limit/trust/inventory/linter exception or native_decide. [pcc:unverified]

Raw reserved-token, empty-constant rewrite, default200000-heartbeat whnf,
nsmul/case/Point.zero interface failures are preserved. Explicit constant-map
equations and the maintained Polynomial.commRing constructor resolve the whnf
interface without raising limits. A JS snapshot typo lost the observed polling
exit for mixed001; no pass was inferred. Mixed002 was checked once with a
durable exit0 status receipt. [pcc:unverified]

All406 older pins and22 published ledger rows remain frozen. New source/prose
and source commit staged whitespace checks have zero findings; immutable older
raw whitespace receipts are referenced instead of recursively recopied. No
scientific/numerical/field/curve/Sage/LLL/native qualification, paid job, image
build/pull or control execution. Earlier scientific control stays UNEXECUTED,
with live cost and actual runtime admission missing. [pcc:unverified]
