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
   actual Weierstrass norm/intersection semantics already in Mathlib. [pcc:unverified]
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

## Simplification before the projective-product law

For the actual pair of anchors T and -T, both have the same abscissa a.
After direct handling of their input buckets, choose v(P)=x(P)-a and
z_T(P)=(y(P)-y(T))/v(P), likewise z_-T. These are valid for every remaining
input point, with no N+M<p restriction or pencil-slope search.

    D_U(P,Q)=-v(P)*v(Q)*(z_U(P)-z_U(Q)).

In the product D_T*D_-T, the minus signs and v factors are squares. Hence
the quadratic carry is exactly the character of the product of the two
key differences, and its rectangle product uses just the two indexed
resultants. This removes chart-preparation work and the cardinality
restriction from the original prospective version; it does not change
the pair predicate or its nonzero-domain/special-case obligations.

The intended missing generic product law still allows arbitrary unary
scales and retains every indexed factor. This simple actual specialization
will use square-character cancellation. No claim or old frozen input was
edited by this unpinned prospective refinement.

## Prospective carry-character assembly before its first Lean edit

The structure is an actual Mathlib WeierstrassCurve.Affine over a finite
field, its Equation and nonvertical addition polynomial, and the existing
quadraticChar. Apply addPolynomial_slope/C_addPolynomial as in the already
passing scratch norm assembly003; do not re-prove their curve laws.
Apply the generic map_mul instance for MulChar and quadraticChar_sq_one to an abstract norm
equality with the two input factors nonzero. That is the first floor;
then combine it with the actual Weierstrass norm and ZMod p endpoints. [pcc:unverified]

Missing reusable glue: the generic evaluation norm interface and its
quadratic-character consequence. They belong in Curve.CharacterCarry
first, not in a curve-specific study. Inheritance: actual point equations
from Equation/Nonsingular, reflected ordinate from negY, third abscissa
from addX/slope, norm from polynomial evaluation of existing factorization,
character multiplication/square cancellation from existing MulChar laws.
The input nonzero assumptions match the direct +/-anchor handling; no
new output-density, point-distribution or many-gate hypothesis is inserted.
One compiler at a time, keep failed sources/logs, no limit/linter/trust
changes. The hand cover/descent/cost obligations remain explicitly separate.

Before writing the slope-key law: over a field, let v_i=x_i-a and
d=x1-x2, all nonzero. Existing fraction arithmetic expands
(v1*v2/d)*((y1-b)/v1-(y2-b)/v2) to the numerator/d. Ring normalization
identifies it with b-((y1-y2)/d*(a-x1)+y1), the chord evaluation.
This generic scalar interface belongs in ProjectiveProducts; the actual
curve law merely substitutes slope_of_X_ne. Compile that field assembly
in CharacterFloor before the owner law. Character product transfer also
belongs in that generic module; CharacterCarry owns only curve norm and
the resulting point-gate endpoint. Inverse pairs can be checked directly
first, as can coincident pairs; no nonvertical formula is applied to them.


## Prospective one-mask refinement, before its first Lean edit

The saved derivation in character-row-parity-refinement001 is the intended
algorithm now. Compute all row parities M*c for a single random column mask,
then scan one odd row. A nonzero row functional gives success at least1/2;
t bounded independent masks give miss at most2^(-t). No emptiness certificate.

1. Structure above: univariate polynomials over any commutative ring,
   Polynomial.taylor (translation) and indexed products; finite additive
   groups, homomorphisms into ZMod2, and actual finite F2 matrices/mulVec.
2. Theorems used unchanged: taylor_mul, taylor_pow, taylor_apply,
   coeff_X_pow_mul, taylor_coeff_zero; ShortlistCompletion.fiber_card_mul,
   BilinearSketch.surjective_of_value_one; Fintype.card_le_of_injective;
   Matrix.toLinearMap₂'_apply', dotProduct_single and matrix mulVec laws.
3. Object: F(X)=(X-Cu)^m*g(X), including m>=characteristic. Its mth
   translated coefficient equals g(u). For masks use f:C->+ZMod2 with a
   value1, any containing success predicate S; actual S(c) is M.mulVec c!=0.
4. Assembly first: over a generic CommRing, shift the known repeated root
   and apply the coefficient law; instantiate at ZMod p with Fact p.Prime.
   Generic half-count uses inherited fiber cardinality and injective subset
   inclusion; actual matrix endpoint uses the already checked bilinear
   matrix interface and mulVec, not a new group-count argument.
5. Missing components only: generic root-stripping Taylor coefficient,
   generic containing-predicate half-count and actual matrix-vector endpoint.
   Build in owner modules first; no study-specific copy. Hand algorithm
   exception correction and complexity are separate from compiled theorems.
6. Inheritance table:

| Operation | Floor law | New glue |
|---|---|---|
| Translate a repeated factor | taylor_mul, taylor_pow, taylor_apply | X-Cu translates to X |
| Extract first surviving coefficient | coeff_X_pow_mul, taylor_coeff_zero | substitute repeated factor |
| Count masks hitting1 | existing fiber_card_mul | include fiber in S |
| Read an actual row parity | toLinearMap₂'_apply', dotProduct, mulVec | specialize row unit vector |
| Half of masks detect nonzero | generic containing-predicate count | apply to actual matrix |

Proof chain: taylor u ((X-Cu)^m*g) = X^m*taylor u g;
coefficient m equals coefficient0 of taylor u g; equals g.eval u.
No derivative/factorial inversion or characteristic bound is permitted.
Count chain: |fiber1|*2=|C|; |fiber1|<=|S|; so |C|<=2|S|.
If a row functional is1, M*c cannot be0 by the existing row-evaluation law.

Cost/exception contract before implementation: selected column records are
independent mask coordinates even when point values or projection keys
repeat. For each DISTINCT row key u, let m_u count selected column records
at u. Sum_u(m_u+1)<=M+N. Compute residues modulo (X-u)^(m_u+1) using the
primary product/remainder tree; compute each truncated Taylor shift by
divide-and-conquer polynomial translation, valid in every characteristic.
For f=f_low+X^k*f_high, translation is translation(f_low)+(X+u)^k*
translation(f_high); no factorial formula. Summed degree cost is quasilinear
up to logs, including the initial remainder of F if needed. This is hand
accounting with standard fast univariate arithmetic, not a measured program.

Per row, the union of zero-key partners is contained in the known point
values P,T-P,-T-P. Strip zero factors separately at each anchor by the
Taylor law, then divide out ONLY NONZERO factors from this union's buckets
which remain at the other anchor. Retain all multiplicities. Remove their
unary signs/counts as well. At most three point-value corrections per row;
all divisions must carry explicit nonzero checks. Direct input O,+/-T,
coincident pairs and inverse pairs are scanned first. A recovered indexed
pair is checked against actual curve addition. Many-bit AND and useful
relation yield are not supplied by this single-character primitive.


## Indexed root stripping and forbidden-set correction: prospective floor

Before either new law: structure is Finset-indexed products over CommRing
(for factorization/Taylor) and Field (for nonzero cancellation). Existing
Finset.prod_filter_mul_prod_filter_not partitions the ACTUAL record index
set. taylor_strip_root supplies the translated coefficient; no repeated
root enumeration law is re-proved. Objects are s:Finset I, u:I->R and an
anchor a, and separately s,u:I->F, arbitrary forbidden predicate B.
Assembly floor first uses exactly this partition identity and generic
Taylor law; instantiate the resulting indexed coefficient at ZMod p.
Missing glue: expose the coefficient after splitting equal keys; expose
nonzero-product quotient after removing B, with all kept u nonzero.
These belong ProjectiveProducts and are not curve-specific facts. [pcc:unverified]
Inheritance: filter partition by the existing product law, equal-key
factors by substitution and prod_const, coefficient by taylor_strip_root,
nonzero denominator by prod_ne_zero_iff, cancellation by div_eq_iff.

Chain1: full product = equal-key product * other-key product
= (X-Ca)^(equal-key count) * other-key product. Apply the existing Taylor
coefficient law, then eval_prod/eval_sub/eval_X/eval_C. Chain2: partition
the nonzero-factor index set by B; its not-B part equals s.filter(not B)
by the supplied nonzero-on-kept hypothesis. Product of B's nonzero factors
is nonzero. Divide to recover the kept product. Apply this scalar law
once per anchor and multiply. This retains repetitions and never divides
by a zero projection factor. No curve/sampling assumption is hidden here.


Actual-instance normalization: the two ZMod p indexed laws need convert/congr
to identify hidden finite-filter/operation instance presentations. Existing
filter_congr_decidable alone did not close both endpoint types. Focused
actual-instances004 passes with structural congruence only; it does not
rerun the generic factorization or correction proof. Preserve the full
gate001 and actual-instances002/003 failures. No hypothesis, proof limit,
trust or linter policy change.
