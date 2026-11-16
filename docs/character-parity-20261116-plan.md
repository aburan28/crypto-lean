# Single-character pair search by rectangle parity: prospective plan

16 November 2026. Continue the user's new-mechanism research. No native
numerical, qualification or paid execution. The original complete classical
subexponential prime-field ECDLP criterion remains unchanged and unmet.
This candidate is a specific single-character witness-search algorithm;
it does not assume that a many-bit sieve follows from one bit.

## Discriminating question and prediction

Can a single elliptic quadratic-character join be searched through exact
rectangle parity, without evaluating every pair? Prediction: yes on the
stated nonzero charts, because the product of chord determinants is a
univariate resultant. A nonzero F2 Boolean adjacency matrix has a random
row/column-mask parity equal to1 with probability at least1/4. Subdivision
then finds an actual passing pair. No random-distribution assumption on
the input points or selected outputs enters this probability.

The target is a fully specified primitive with bounded attempts and
failure at most(3/4)^t when a passing pair exists. A failure output means
no witness found, not an emptiness proof. Every returned pair is checked.
Give a charged quasilinear field-operation bound from primary univariate
resultant algorithms; this is not an ECDLP speed bound or measurement.

## Actual pair predicate

Over an odd prime field, fix an actual curve point T and its inverse -T.
Set kappa(P)=chi(x(P)-x(T)), excluding zero factors for the main chart.
Mathlib's existing addition-polynomial law, evaluated at T, gives the
working norm identity checked in the separate CarryFloor assembly003.
For a chord/tangent P,Q and R=-(P+Q), line values obey

    ell(T)*ell(-T)=(x(P)-x(T))*(x(Q)-x(T))*(x(R)-x(T)).

For distinct affine points, let D_T(P,Q) be the3x3 determinant of their
homogeneous point rows and T. The normalized line denominator occurs
squared, so

    kappa(P+Q)=kappa(P)*kappa(Q)*chi(D_T(P,Q)*D_-T(P,Q)).

The new main-chart pair predicate is the right-hand side equal to+1.
Its unary signs and both determinants are explicit point-only data.
Infinity, input+/-T and coincident pairs are handled separately. Inverse
pairs use the vertical-line case, not the nonvertical slope formula.
Keep full primitive records and multiplicities with every point bucket;
this primitive only finds a gate-passing pair, not a useful final relation.

## Product oracle and random isolation before code

For each anchor U in {T,-T}, choose a line L_U through U avoiding all
remaining input points. When N+M<p, at most N+M forbidden pencil slopes
allow this choice from N+M+1 distinct candidates. Define

    v_U(P)=L_U(P),  z_U(P)=(x(P)-x(U))/v_U(P).

The elementary determinant identity gives

    D_U(P,Q)=v_U(P)*v_U(Q)*(z_U(P)-z_U(Q)).

For any record-index rectangle A x B with nonzero determinants, define
F_A(X)=prod_P(X-z_U(P)), F_B(X)=prod_Q(X-z_U(Q)). Including all repeated
record factors, the product is

    prod_(P,Q) D_U(P,Q)
      =(prod_P v_U(P))^|B|*(prod_Q v_U(Q))^|A|*Res(F_A,F_B).

Let h(P,Q) be the +/-1 gate value above. The product of -h over a rectangle
is(-1)^(number of passing pairs). Its value is obtained from two resultant
characters, unary sign products and(-1)^(|A|*|B|). Thus an odd value is a
certificate that a pair exists, without listing the rectangle.

Randomly retain each row and column independently with probability1/2.
For the actual F2 adjacency matrix M, parity is r^T M c. If M is nonzero,
choose an entry1. A half-sized affine row slice has a nonzero column
functional; on those rows, half of column masks give parity1. Existing
equal-fiber cardinality laws therefore give at least1/4 of all raw masks.
At most t independent trials yields miss probability at most(3/4)^t.

After an odd rectangle, split its larger dimension in half. Test one
subrectangle; if it is even, its complement is odd. Each two-way step
preserves oddness. Stop at a single row/column and independently check it.
The sum of the side lengths on this path is O(N+M), because halving the
larger side shrinks their sum by at least a quarter.

## Removing zero determinants without quadratic work

Do not call a zero resultant a parity bit. After direct handling of
infinity, input +/-T and coincident-point buckets, a zero determinant
means P+Q=T or P+Q=-T. These are two point-value matchings. Coincidence
is a third matching already tested directly. Store complete provenance
buckets and use point identifiers for this decomposition.

The complement of each matching is covered by at most2*ceil(log2(D+1))
rectangles: choose a differing bit of the forbidden partner identifier
and the actual column identifier, and its orientation. Intersect the
three covers. The resulting O(log^3(D+1)) rectangles cover all remaining
allowed pairs and contain none of the forbidden edges. Full record
multiplicities remain; overlapping cover rectangles are not a count
partition. Existence search tolerates duplicate coverage and charges it.

With t masks per rectangle and primary quasilinear univariate product/
resultant arithmetic, the hand target is

    O~(t*(N+M)) field operations,

where the tilde includes the matching cover and polynomial arithmetic
logarithms. Include polynomial(log p) bit costs, point/key preparation,
random bits, direct special cases and witness recovery. No fast multivariate
resultant, hidden Cartesian-product construction or measured speed is used.

## Six-field instance gate before first Lean edit

1. Structures: finite additive groups and homomorphisms into ZMod2;
   finite Sigma/subtype counts; univariate polynomials over a field;
   actual Weierstrass norm/intersection semantics already in Mathlib.
2. Existing laws as stated: ShortlistCompletion.fiber_card_mul;
   AddMonoidHom.flip; Nat/Fintype Sigma cardinality; card_le_of_injective;
   Polynomial.resultant_prod_left, resultant_X_sub_C_left and polynomial
   evaluation; finite product distribution. Do not re-prove those laws.
3. Objects: B:R->+(C->+ZMod2) with a supplied entry B(r0)(c0)=1 for the
   generic mask-count theorem; actual matrix parity is its instance. For
   the product oracle use indexed key arrays (repetitions retained), not
   just their distinct roots.
4. Floor: compile application of equal-fiber scaling to both row/column
   maps and of existing resultant laws to products of X-C(key). Reuse
   actual field/curve assembly003 for the norm interface, without copying
   its underlying curve proof. Then instantiate resultants at ZMod p.
5. Missing only: generic quarter-success bilinear sketch count and a
   projective determinant-product scaling interface. Shared generic laws
   live in crypto-lean first. Algorithmic covering/descent/cost and the
   multi-character extension remain separate proof obligations.
6. Inheritance:

| Operation | Existing floor | Missing glue |
|---|---|---|
| Nontrivial mask slice | equal-fiber scaling, ZMod2 two-element field | specialize a value1 |
| Count successful mask pairs | Sigma card, injective inclusion | quarter-count endpoint |
| Indexed root product | resultant_prod_left, X_sub_C | direct application |
| Determinant scaling | finite prod_mul_distrib | explicit projective factors |
| Actual curve carry | addPolynomial_slope and C_addPolynomial | assembly003 already checked |
| Locate a pair | parity under disjoint partition | search invariant/cap, pending |

All new laws need actual-instance probes, final canonical audit and named
axiom output before publication. One Lake process at a time; preserve every
failure/source under fresh receipt names. No limit, trust, inventory or
linter changes. The unrelated ProjectiveVeluInstanceProbe.lean stays alone.

## Controls, scope and primary review

Controls: empty lists; all-even total parity with a nonempty matrix; a
single passing pair; duplicate records; projection-key multiplicities;
coincident/inverse points; zero carry; all-zero/all-one mask matrices.
No numerical experiment is authorized or planned here; the first tests
are symbolic inherited-law and finite-count compiler assemblies.

Multiple character constraints are NOT an immediate application: the
parity of an AND of bits is not determined by the individual parities or
parities of their XORs. A valid many-bit oracle must be built explicitly;
materializing early dense matches may erase the benefit. Nor is this a
full-root useful-yield argument. Keep the complete-algorithm gap visible.

KB unavailable. Re-read Dechene and full Galbraith--Smith for the curve
carry/context, plus exact Mathlib resultant and finite-fiber declarations.
Read Moroz--Schost, A fast algorithm for computing the truncated resultant,
https://cs.uwaterloo.ca/~eschost/publications/resultant_series_final.pdf,
introduction: ordinary UNIVARIATE field resultants are quasilinear; its
bivariate/truncated theorem is not the bound used here. FLINT docs are a
navigation aid, not sole proof of complexity. The random bilinear mask
argument is the standard nonzero-linear-functional principle behind
Freivalds; no novelty claim. Searches for character/resultant rectangle
search did not provide a novelty audit; do not say it is new literature.
