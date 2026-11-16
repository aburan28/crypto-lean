# A certifying, capped saturation candidate

16 November 2026. Source-writing and mathematical specification only.
No Sage/LLL, numerical/native curve case, benchmark, qualification or paid
execution is authorized in the retained scope. Sage is absent from PATH.
The code will be an UNEXECUTED research prototype, not a subexponential
algorithm claim. Existing PR25 remains the owner PR to extend; preserve all
106 frozen subjects and eleven ledger rows. No unrelated Velu probe edits.

## Question and falsifiable fork

Can modular denominator saturation produce useful, certified short integer
relations on the projective quotient, where the ordinary balanced ideal
cannot meet the HHG sufficient test? Competing outcomes are (a) no short
relations; (b) short relations but positive-dimensional quotient; (c) finite
quotient, but no checked original point decomposition; (d) checked useful
decompositions. Record every stage, failure, cap and original multiplicity.
None of these outcomes is asserted before execution.

The executable candidate must include fixed-factor-base generation,
label-blind decomposition of random mixed targets, factor-base cancellation,
and final scalar verification. It may return a capped failure. The missing
asymptotic success/yield bound remains essential to the original criterion.

## Literature first and choice of algorithm

KB MCP remains unavailable; bounded owner/Mathlib and primary fallback.
Ryan2025 primary chapter3 and cuso pinned source
fb2747d2105a8e48499bf10a3a717cf80c14d079 were read. Fixed monomial/ideal
optimality is distinct from root independence. This first prototype uses a
bounded Macaulay shift family as an explicit control; it does NOT implement
or claim Ryan's optimal D-Groebner shift algorithm. Its norm certificate is
the exact integer L1 sufficient bound, as in cuso's default HHG path.

Sage official documentation was checked for ideal.saturation, polynomial.lift,
integer Matrix.LLL(transformation=True), dimension/variety and rational root
recovery interfaces. The source must verify every returned lift and LLL
transformation before promoting a result. No opaque return is a proof.

CHHS2016 arXiv1605.08065 primary theorem4/21 and section4, and CHHS2021
arXiv2111.14180 introduction/independence scope, were read. Pure binomial
auxiliaries can vanish on the whole integer search interval with huge degree;
the univariate low-degree theorem requires a small modulus factor. These
results do not prove a multivariate S3 impossibility. No factorial division
is allowed without an integer-value certificate. Binomial bases are not
quietly substituted into this prototype.

## Data and stage contracts

Input: public p>3, short curve a,b, known total order N=h*r with r odd prime
and gcd(h,r)=1, nonzero G of orderr, Q in that subgroup. Validate the point
count and subgroup contracts in the future capped worker. The unique
r-primary subgroup avoids silently assuming arbitrary r-torsion is <G>.
This prototype does not cover every exceptional subgroup structure.

Build one canonical point per interval x in [0,B), keeping only r-torsion
points. Fix the catalog before drawing targets. Keep every catalog index
and every repeated occurrence/sign in a returned tuple. Precompute a capped
signed two-sum control. Draw alpha,beta uniformly and form R=alphaG+betaQ;
pass only R and the fixed catalog to the selector, never alpha,beta.

For lengths3 through m, construct the homogenized S3 path with U_i/V_i.
The ordinary input is F_1,...,F_s. In saturated mode, over Fp compute
I:(product V_i)^infinity and a finite exponent n. For each generator g,
obtain and VERIFY the exact polynomial identity D^n*g=sum A_i*F_i.
Reject an exponent, degree, term count or coefficient size above the cap.
Lift g's coefficients to centered integers. It is a valid modular relation
at every original root with nonzero denominators. Ordinary mode retains
the original generators for the paired control.

At fixed multiplicity t and shift degree d, enumerate only a declared
finite family p^(t-|e|)*product(g_i^e_i)*monomial. Preflight its full row
count, charge all rows, and group by projective multidegree. Reject a
nonhomogeneous generator rather than assuming scaling invariance. For each
block, encode weighted integer coefficient rows, enforce rank/column/cell
caps, and compute LLL with its transformation. Verify T*A=R exactly.
Reconstruct polynomials only when scale divisibility holds. Promote a
nonzero row only if sum |c_m|*X^m < p^t, using integers, with its complete
row-combination witness retained. No floating norm or heuristic promotion.

Only after homogeneous integer vanishing is certified, set V_i=1, then
eliminate ratio coordinates over Q with a checked lexicographic Groebner
basis. Require a finite bounded LEAF standard-monomial staircase before
rational root enumeration. Unused/projected ratios need not be enumerated.
Sage's current official documentation
warns that vector_space_dimension can have a 32-bit overflow, so its scalar
return is not a safe admission cap. Check the Groebner membership/critical
pairs and enumerate the downward-closed staircase with a hard cap; an
unfinished enumeration is a capped failure. Test integer leaves against the
fixed catalog, then enumerate capped original point signs. The projection
can include extra leaves or points outside the bounded-height chart; a
decomposition is accepted only after sum(sign_j*catalog[id_j])=R on the
actual curve. This sound overapproximation does not claim bounded-ratio
reconstruction or root-search completeness. Do not call a positive-dimensional
or capped attempt an emptiness proof.

Accumulate checked relation rows c with R=alphaG+betaQ. Incremental modular
elimination keeps original target-index provenance. A dependence cancels
the factor base and gives A G+B Q=O; recover -A/B only when B!=0 and verify
the scalar by multiplication. The newest relation has coefficient1 in its
dependence before normalization, so that target-index vector is nonzero.
The existing SingleRelation.mixedLabelFiberEquiv and recover_from_relation
own the conditional label/recovery laws; do not reproduce them for a curve.
Conditional on a fixed catalog and a selector seeing only point values,
the standard free-label argument gives useful B with probability1-1/r.
The actual decomposition success probability and its runtime remain unknown.

## Resource and evidence contracts

Use a parent process-group deadline, CPU/address-space/output limits and
the future EKS container memory limit. Cap field bits, catalog size, point
and sign trials, saturation exponent/terms/degree, all shift rows, columns,
matrix cells, total lattices, root degree and target attempts. One global
budget spans every length/block/failed query. A timeout is a capped failure,
never absence. Fresh output directories/files only; JSON polynomial terms
are data, no eval or shell interpolation. Preserve inputs, versions, raw
stage evidence, accepted relations and scalar check. A separate verifier
rechecks catalog membership, each point relation and the final scalar without
running saturation, LLL or root recovery.

Allowed verification now is static source parsing and metadata/interface
review only. No numerical success, speed, rank trend or complete algorithm
is inferred from unexecuted code. Any later execution needs the existing
admission/backend/budget rules and a frozen, reviewable trial plan. No
independent signed PCC verification or evaluated identity certificate exists.

## Concrete implementation choices after the interface read

Use Sage's Fp ideal.saturation(principal_ideal_D), returning an ideal and
exponent n; VERIFY each D^n*g with polynomial.lift against the original
generators and an exact dot-product equality. No unproved lift is accepted.
Use a local bounded Macaulay implementation, not copied cuso code; cite
cuso's pinned API/default-L1 behavior as source context. No L2/float branch.
Keep all standard-monomial cap logic in a dependency-free metadata helper
so cap/termination controls can be checked without importing Sage or doing
curve/lattice computations. Actual worker stages remain unexecuted.

The end-to-end worker fixes the interval catalog before label draws and
passes only R to decomposition. Preserve original target-index coefficients
through incremental field row elimination; a new dependent row has newest
provenance entry1, so its original target vector is nonzero. Its factor-base
cancellation gives A G+B Q=O; validate -A/B by actual multiplication. Do not
ask for full factor-base rank when a useful dependency suffices. The unknown
decomposition yield is not removed by this standard free-label argument.

Future ordinary/saturated controls must share an external frozen query-label
panel; raw accepted and rejected targets remain, not only soluble cases.
No concrete curve panel is generated or executed in this source-only phase.

Label metadata must not change the selector's byte budget: use fixed-width
decimal encodings for alpha,beta and recovery/dependence scalars. The algebraic
free-label probability statement is conditional on its uniform/label-free
hypotheses; no such distribution theorem is asserted for wall-time-interrupted
or otherwise censored pilot runs. Every final scalar still requires its own
exact curve check.


## Successor fork: explicit local minors and subcritical translated charts

Source-review extension,16 November2026; no numerical job. Keep the original
paired ordinary/global-saturation pilot and its inputs unchanged. Add a
local_minors source mode with explicit V,V²,V³ certificates, plus a separate
bounded chart-offset panel interface. These are source candidates only.

The first local-minors hypothesis is REJECTED at balanced height for chain
length at least4: every nonzero added generator has total projective degree
at least2. A boundary linear subresultant has degree1 in its eliminated
slot and degree2 in its neighbor; its resultant has degree4 in that neighbor.
Interior versions have more projective degree. The existing generic
filtration therefore still excludes an HHG-short row. Length3 is an explicit
exception. Keep the mode as a falsifiable negative control; do not present
its constant degree alone as a selector breakthrough.

A distinct positive opening uses H=floor(sqrt(p)/2) and x_i=tau_i+U_i/V_i.
For positive primitive pairs 1<=u,v<=H with H²<p, rational reduction is
injective. A union bound over common divisors gives at least H²/4 pairs.
For fixed x and uniform tau in Fp, the representable probability is at least
H²/(4p). Independent offsets across s=m-2 slots therefore retain any fixed
finite intermediate tuple with probability at least(H²/(4p))^s. For p>=16,
H>=sqrt(p)/4, so this is at least64^(-s). An iid pool of
N>=64^s*(s*ln(p)+ln(1/epsilon)) offset vectors simultaneously covers all p^s
finite tuples with failure probability at most epsilon. This is hand
counting and the existing generic pool logic, not a new compiled theorem.

Use the original polynomial system with (U+tau V,V) substituted per slot.
This is coordinate translation, not group translation, and requires no
character-sum or selected-output uniformity assumption. Keep infinity cases
separate. The old H>=sqrt(p) obstruction does not apply. This does not prove
short rows exist: coefficient height, determinants, equation independence,
finite projection, all branch costs and useful random-target yield remain.
The prototype accepts only a capped externally frozen offset panel; it does
not generate or claim the asymptotic covering pool in the numerical code.
