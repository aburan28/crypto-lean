# One-character elliptic pair search by row parity

16 November 2026. A construction prompted by the request to try different
fast-selector ideas. The design computes a binary matrix-vector action
without materializing all pairs, using two univariate product/remainder
trees and repeated-root Taylor coefficients. Shared algebraic components
and actual prime-field instances compile locally. The [diagram](character-parity-20261116/flow.svg),
[PDF](character-parity-20261116/report.pdf) and
[publication record](character-parity-20261116/PUBLICATION.md) accompany the source. The search and its cost
are hand derivations, not an implemented or measured selector. [pcc:unverified]

## Input, output and guarantee

Input: an elliptic curve over F_p, p>3, an affine nonsingular anchor
T=(a,b), two explicit lists of nonsingular group points A,B of lengths N,M,
and an integer trial cap t>=0. Every list record keeps its original index,
full provenance and multiplicity. Let chi be the quadratic character and

    kappa(O)=1; kappa(P)=chi(x(P)-a) for affine P.

Return original indices i,j with kappa(A_i+B_j)=1, checked by actual group
addition, or NO_WITNESS_FOUND. On any fixed input containing a passing pair,
t independent uniform column-record masks miss with probability at most
2^(-t). No input or selected-output distribution assumption is used. A
failure output is not an emptiness certificate. [pcc:unverified]

The derived worst-case cost is O~(t*(N+M)+N+M) field operations and
polynomial(log p,log(N+M)) overhead for bit arithmetic, with standard fast
univariate arithmetic. Point preparation, multiplicity bookkeeping, all
failed masks, random bits, exceptional cases, recovery and checking are
included. These are symbolic bounds, not timings or a speed comparison.
For an empty list return immediately. [pcc:unverified]

## Why actual curve addition supplies a product predicate

Write -T=(a,b_minus); on a general Weierstrass model b_minus=negY(a,b).
For a nonvertical chord or permitted tangent through P,Q and
R=-(P+Q), Mathlib's addition-polynomial factorization, evaluated at T, gives

    ell(T)*ell(-T)=(x(P)-a)*(x(Q)-a)*(x(R)-a).

The nonvertical main chart has x(P),x(Q)!=a and x(P)!=x(Q). Put

    z_plus(P)=(y(P)-b)/(x(P)-a),
    z_minus(P)=(y(P)-b_minus)/(x(P)-a).

Each anchor line value has the common scale
s=(x(P)-a)*(x(Q)-a)/(x(P)-x(Q)). Their product contains s^2. Multiplicativity
and chi(s^2)=1 give the exact identity

    kappa(P+Q)=kappa(P)*kappa(Q)*chi(d_plus(P,Q)*d_minus(P,Q)),
    d_sign(P,Q)=z_sign(P)-z_sign(Q).

The shared line_norm, quadratic_norm and quadratic_key laws implement this
chain; ActualInstances applies it to the sum of actual nonsingular points
over ZMod p. Output character0 is allowed in this identity. No generalized
Jacobian lift, hidden scalar, special embedding degree or coprimality of
the curve order with p-1 is required. [pcc:unverified]

## Direct cases and the finite forbidden set

Build point-value dictionaries carrying all original records. For each
input value in {O,T,-T}, scan the opposite list and return a passing indexed
pair if present. There are at most three such values on each side, so these
scans are linear. If none passes, exclude their buckets from active search.
Scan coincident point values across the lists and test kappa(2P); return if
it is1. Inverse pairs P,-P always pass because their sum is O, so a dictionary
lookup returns such a pair if present. These steps cost O~(N+M) and do not
discard any passing pair after an unsuccessful scan. [pcc:unverified]

Remaining same-abscissa pairs are coincident. They were tested and failed.
For a remaining row P, a zero in either projection difference occurs only
at the point values

    D(P)={P, T-P, -T-P}.

Deduplicate this set of at most three POINT VALUES. A distinct nonvertical
zero means collinearity with one anchor: the group sum is T or -T. Both
have character0. Coincidence is the separately tested case. Conversely,
any remaining pair outside D(P) has two nonzero differences and the exact
main-chart formula. These facts use the chord/group law and the two roots
of the Weierstrass equation at a fixed abscissa. They are a hand exceptional-
case argument; they are not claimed as additional formal theorems. [pcc:unverified]

Every original pair in these excluded buckets is nonpassing once direct
search finishes unsuccessfully. Bucket reuse retains full record identities
and multiplicities; it never samples one bit per distinct point value.

## One mask: all row parities without all pairs

Independently retain each active COLUMN RECORD with probability1/2. Call
the selected record-index set S. Aggregate selected counts n_Q by point
value, retain all selected indices, and form the two indexed polynomials

    F_sign(X)=product_(j in S)(X-z_sign(B_j)).

For each DISTINCT row key u, count m_u selected columns with that key.
The exact repeated-root identity is

    [X^m_u]F_sign(X+u)
       =product_(j in S: z_sign(B_j)!=u)(u-z_sign(B_j)) = H_sign(u).

This is a Taylor/Hasse coefficient, not an ordinary derivative divided by
m_u!. It works for every natural multiplicity, including m_u>=p.
indexed_taylor_nonzero proves it over any commutative ring. [pcc:unverified]

For each row P, set d_sign(P,Q)=z_sign(P)-z_sign(Q) and compute

    C_sign(P)=product_(Q in D(P), d_sign(P,Q)!=0) d_sign(P,Q)^n_Q,
    G_sign(P)=H_sign(z_sign(P))/C_sign(P).

Only nonzero factors enter C_sign. The two zero-stripped products removed
zeros separately; this quotient also removes forbidden factors that were
nonzero at the other anchor. The generic nonzero_product_correction law
proves each quotient equals the product over admissible selected records.
It proves the denominator nonzero. There are at most three point-value
corrections per row, even with arbitrary original record multiplicities.
[pcc:unverified]

Let k_P=|S|-sum_(Q in D(P))n_Q and let U_P be the product of kappa(B_j)
over admissible selected records. Compute U_P from the selected global sign
product by removing these same at most three bucket contributions. All
active unary signs are nonzero. The row sign is exactly

    R_P=(-1)^k_P * kappa(P)^k_P * U_P * chi(G_plus(P)*G_minus(P)).

For h_j=kappa(P+B_j) in {+1,-1} on admissible records, R_P=product_j(-h_j).
Thus R_P=-1 iff this row has an odd number of passing selected columns.
Together these bits are M*c over F2, where M_ij=1 precisely for a remaining
passing indexed pair and c is the raw column-record mask. [pcc:unverified]

If an odd row exists, scan its selected original column records, skip its
forbidden buckets and check actual curve addition. Oddness ensures a passing
pair is found. Return the original indices. An implementation that finds no
pair after an odd sign must report an internal inconsistency, not silently
turn the parity calculation into an emptiness assertion. If no row is odd,
continue to the next independent mask, up to t trials. [pcc:unverified]

## Explicit fast polynomial subroutine and cost

For one anchor, the sum of m_u+1 over distinct row keys is at most |S|+N:
each selected column contributes to at most one queried key. Construct the
monic moduli (X-u)^(m_u+1), their product tree and the corresponding remainder
tree. Reduce F at the root first if needed. This computes

    F(X) mod (X-u)^(m_u+1)

for every queried key with total modulus degree O(N+M). Translate each
remainder by u and read coefficient m_u; the omitted multiple of
(X-u)^(m_u+1) cannot affect that coefficient. [pcc:unverified]

Translation itself needs no factorial formula: split a polynomial as
f_low+X^k*f_high, recursively translate its two pieces and combine them as
shift(f_low)+(X+u)^k*shift(f_high). Binary powers and fast polynomial
multiplication give quasilinear cost up to logarithms over any field.
Summing these leaf costs is quasilinear in the total modulus degree.
Monic division/remainders use standard reversed-series/Newton arithmetic;
the product/remainder-tree recursion is the primary Borodin--Moenck method.
The variable-degree accounting here is explicit, not an imported uniform-
degree theorem. Standard polynomial/integer multiplication supplies the
polynomial-logarithmic bit factor. [pcc:unverified]

Each anchor costs O~(N+M) per mask. Dictionary counts, three corrections
per row (binary exponentiation charges log M), unary signs, character
evaluation, t*M random bits and one O(M) witness scan obey the stated cap.
No bivariate resultant, generic multivariate multipoint oracle, uncharged
Cartesian product or large implicit list is used. Space is quasilinear in
explicit input size for sequential masks and product/remainder trees.
[pcc:unverified]

## Probability without a sampling hypothesis

After failed direct search, any passing pair is an entry1 of the fixed
remaining binary matrix M. Fix a nonzero row. Its map c -> (M*c)_i is a
surjective additive homomorphism to F2, hence exactly half of all raw masks
give1. That one-fiber is contained in {c:M*c!=0}. The shared half_count and
matrix_half_count laws apply existing equal-fiber cardinality unchanged.
Therefore each independent mask succeeds with probability at least1/2;
t masks miss with probability at most2^(-t). The returned pair is checked,
so no false positive is accepted. [pcc:unverified]

The earlier two-mask rectangle construction and quarter-count remain in
the prospective plan and receipts. The all-row method improves its success
bound and avoids the earlier rectangle cover/descent. Its matrix law is
the standard nonzero-linear-functional principle, not a novelty claim. [pcc:unverified]

## Requirement and evidence boundary

| Requirement | Evidence or remaining work |
|---|---|
| Try different selector ideas | Three mechanisms in alternatives001; carry route developed constructively |
| Actual prime-field elliptic predicate | Shared curve laws plus actual point-addition assembly |
| Repeated records and keys | Indexed Taylor and correction laws, no squarefree assumption |
| Bounded one-character witness search | Full hand procedure/cost/probability above; executable implementation not supplied |
| Multiple simultaneous gates | No fast Hadamard-conjunction matvec is supplied |
| Useful m-color relation and complete ECDLP algorithm | Implicit-family construction, extraction, label/provenance compatibility and useful-yield bounds remain open |

Individual gate parities, or all subset XOR parities, do not determine the
parity of their AND. A product of quadratic characters is an XOR condition,
not simultaneous residue membership. For two binary matrices, the parity of
the entrywise AND count is trace(M1*M2^T); separate cheap matvecs do not by
themselves supply a cheap exact trace. The next construction must exploit
the actual algebraic pair structure to implement conjunction, or devise a
selector whose required gate already has a cheap aggregate. [pcc:unverified]

The user's complete end-to-end algorithm criterion is unchanged and unmet.
No new native numerical, paid or qualification execution was performed.
No success distribution, fitted exponent, measured speedup or literature
novelty claim is asserted. Existing frozen panels and their access boundary
are unchanged. All older PCC subjects remain preserved. [pcc:unverified]

## Proof map and inheritance

The prospective six fields and failed/passing floor receipts are in
[the plan](character-parity-20261116-plan.md). Shared ownership:

| Named interface | Kind / structure | Inherited law |
|---|---|---|
| surjective_of_value_one | Generic law, additive group to F2 | Two-element codomain |
| half_count; quarter_count | Generic finite group laws | ShortlistCompletion.fiber_card_mul, Sigma/card inclusion |
| matrixSketch_single; matrixSketch_row | Matrix instance obligations | toLinearMap₂'_apply', dot-product laws |
| matrix_half_count; matrix_quarter_count | Matrix endpoints | Generic count laws unchanged |
| taylor_strip_root | Generic CommRing law | taylor_mul/pow, coeff_X_pow_mul, taylor_coeff_zero |
| indexed_taylor_nonzero | Generic indexed CommRing law | prod_filter partition, preceding Taylor law |
| nonzero_product_correction | Generic indexed field law | prod_filter partition, prod_ne_zero_iff, div_eq_iff |
| quadratic_transfer | Generic finite-field law | map_mul, quadraticChar_sq_one |
| secant_key | Generic field scalar identity | Nonzero denominator arithmetic |
| indexed_resultant; scaled_difference_product | Generic indexed field laws | Resultant/evaluation and finite products |
| line_norm | Curve instance obligation | addPolynomial_slope, C_addPolynomial |
| quadratic_norm; quadratic_key | Actual curve endpoints | Generic transfer, slope_of_X_ne, square character |

The table contains17 named theorems and one matrixSketch definition. The
exception-set identification, algorithm, arithmetic complexity and repeated-
trial probability multiplication are hand reasoning, not additional Lean
verification claims. Canonical gate002 audits236 theorems with0 failing and0 trusted-native
exceptions. All17 named compiler axiom prints use only propext,
Classical.choice and Quot.sound (or subsets). See PUBLICATION and the
raw gate002/axioms001 receipts. No fresh independent checker is available. [pcc:unverified]

## Sources checked

KB tools are unavailable in this runtime; bounded repository/Mathlib and
primary-paper fallback was used. No novelty conclusion follows from this
availability gap.

- Existing source A/B/C plans, retained-remainder and translated-intersection
  assessments, selector-tree and color-checksum reports in this owner.
- Mathlib pinned by lake-manifest.json, particularly affine Formula/Point,
  quadraticChar Basic, Polynomial Taylor, Resultant Basic, matrix bilinear
  forms and finite product laws; exact declarations are named above.
- Borodin--Moenck, *Fast Modular Transforms* (1974), pp372--374,
  [primary paper](https://www.cs.toronto.edu/~bor/Papers/fast-modular-transforms.pdf):
  product tree and Modular Form recursion over a Euclidean domain. Variable
  multiplicity and arbitrary-characteristic shifts are accounted for here.
- Moroz--Schost, *A fast algorithm for computing the truncated resultant*,
  [primary paper](https://cs.uwaterloo.ca/~eschost/publications/resultant_series_final.pdf),
  introduction: ordinary univariate resultants are quasilinear. Its
  bivariate/truncated theorem is not used for this input family.
- Galbraith--Smith, *Discrete logarithms in generalized Jacobians*,
  [full paper](https://arxiv.org/pdf/math/0610073), and Dechene,
  [security discussion](https://cacr.uwaterloo.ca/techreports/2006/cacr2006-35.pdf):
  carry/extension context. The final direct norm identity does not rely on a
  generalized-Jacobian DLP transfer or finite-field embedding.
- Petit--Kosters--Messeng2016 and APS2018, read in the earlier cover-transfer
  review; the separate auxiliary-fiber proposal is not an established solver.

No evaluated identity.certificate/v1 record was issued in this no-numerical-
execution round: its native fixed-modulus evaluation was not run. Generic
Lean source/audit evidence and unverified attestation standing are supplied
separately; no independent-checker or signed verification is asserted.
[pcc:unverified]

No numerical graph is appropriate for proof-only work. The accompanying
editable flow diagram and PDF show the construction; no canonical performance
graph, benchmark table or leaderboard changes follow from this study.
