# Candidate C: prospective four-leaf representation check

2026-11-15. Before the first Lean edit of this component. Continue the
original fast-selector objective; preserve the complete-algorithm criterion.
No numerical/native/paid/qualification execution is planned. Shared PR17
is merged; crypto4311/4338 frozen histories and4352's pending resolver stay
untouched. This independent owner branch starts at56925cee.

## Actual four-leaf model and acceptance

Fix four primitive original records with U=X1+X2 and V=X3+X4. For a raw
independent uniform auxiliary pool T:Fin k->G, use the paired representations

    left_j=U+T_j, right_j=V-T_j.

Every state carries the actual sparse coefficient vector on original and
auxiliary primitive records. Same-tag joining cancels the auxiliary vector;
cross-tag joining leaves its difference. For the original colored contract
that difference must vanish. A cross-tag actual zero relation with a nonzero
full coefficient vector may instead be a valid larger DLP relation, but it
has a different output contract and requires separate costs/yield/recovery.
It must not be mislabeled a formal-zero identity or counted as an original
colored answer. A planted local identity with full vector zero is inadmissible.

Condition on a fixed original valid relation U+V=0 and a symmetric filter
S=-S. Count actual same-tag representations passing BOTH child filters:

    Y(T)=card {j: left_j in S and right_j in S}.

Targets under the raw product-uniform auxiliary law, with delta=|S|/|G|:

    E[Y]=k*delta,
    Var[Y]=k*delta*(1-delta),
    E[Y^2]=k*delta+k*(k-1)*delta^2.

These are prospective statements, not new source results yet. The real-valued
factor k-1 is used in the last expression to avoid an unstated k>=1 guard.
Original-point conditioning and auxiliary cleanliness are separate: never
assume independent auxiliary samples after a rejection condition. Provide
a separate error/conditioning argument if later claiming a clean-pool yield.

Acceptance is the exact coefficient interface, both-gate count, first and
second moments, and a fully charged explicit construction/control. It does
not establish a cheap sampler or a deeper-tree selector. All primitive inputs,
auxiliary construction, failed representations, provenance and final scalar
checks remain charged. No implementation or measured cost is asserted.

## Six-field instance gate

1. Structure above: Mathlib finite additive commutative groups; Finset/Set
   filters; Finsupp primitive coefficient vectors; actual Weierstrass Point
   group/subgroups; uniformOn Set.univ and Measure.pi; real indicator functions,
   expectation and variance.
2. Existing laws used as stated: Point.xRep_neg for actual symmetric coordinate
   filters; group cancellation; Finsupp.single evaluation/injection; uniformOn_univ;
   integral of indicators; measurePreserving_eval and integral_comp_eval;
   ProbabilityTheory.variance_sum_pi; variance_eq_sub; MemLp.of_discrete.
   These give the moment chain. Do not rederive generic variance addition or
   the binomial expectation theorem. Fintype.sum_pow is available as a separate
   finite generating-function identity if an exact distribution is needed.
3. Objects as instances: Y is the actual cardinality of the two-filter accepted
   tag set, not a redefined abstract Bernoulli count. Rewrite it once using
   U+V=0 and S=-S. Each resulting hit is the actual shifted subset indicator
   under the uniform group measure; the sample law is its independent product.
   Coefficient vectors are Finsupp on Fin4 sum Fin k over a nontrivial ring;
   no custom record syntax or erasure map is primary.
4. Assembly probe: type-check the existing product-measure variance and integral
   laws at finite discrete spaces, plus coefficient basis and xRep-neg laws.
   For actual prime-field points inherit finiteness through the existing
   W.nonsingularPointEquiv to WithZero of a finite coordinate subtype; infer
   subgroup finiteness from that, then use Fintype.ofFinite. State DecidableEq
   and the genuine Algebra.Field.ZMod import explicitly. The final assembly
   must instantiate the unchanged shared endpoints at those actual objects.
5. Missing components only: same-tag/cross-tag primitive provenance interface;
   actual two-filter count reduction under the stated relation/symmetry;
   finite uniform shifted-hit mean/variance; product-pool first/second-moment
   endpoints obtained by the existing probability laws. All reusable laws
   belong in the shared owner first. Conditional cleanliness and construction
   costs retain a separately labeled hand scope unless further formalized.
6. Inheritance table:

| Operation | Existing structure/law | New component |
|---|---|---|
| Primitive coefficients | Finsupp over Fin4 sum Fin k | semantic left/right definitions and interfaces |
| Same-tag cancellation | additive group laws | endpoint only |
| Cross-tag residual | single-basis evaluation/injection | endpoint; original-contract distinction |
| Actual adjusted point sums | G AddCommGroup | existing operations |
| Both symmetric filters on a valid relation | negation symmetry + V=-U | accepted-count interface |
| Uniform shifted subset | uniformOn_univ + translation equivalence | mean/cardinality glue |
| Independent raw pool | Measure.pi | existing product measure |
| Variance of its sum | variance_sum_pi | apply as stated |
| Second raw moment | variance_eq_sub | arithmetic read-off |
| Actual curve group is finite | W.nonsingularPointEquiv | instance only |
| Actual coordinate gate is symmetric | Point.xRep_neg | instance only |

## Proof chain before code

1. Expand only the named provenance interfaces; use group cancellation for
   the same-tag sum and single evaluation for the cross-tag residual.
2. From U+V=0 derive right_j=-(left_j). Symmetry makes the two-filter condition
   equivalent to left_j in S. Open acceptedCount only in this interface lemma.
3. Convert its cardinality once to the finite sum of real indicators.
4. Under uniformOn univ, translation is a bijection and the shifted subset
   has cardinality |S|; existing indicator integration gives delta.
5. Indicator squared equals itself; variance_eq_sub gives delta-delta^2.
6. Product-measure coordinate integral and finite-sum integration give k*delta.
7. Apply variance_sum_pi unchanged to get k*delta*(1-delta).
8. Apply variance_eq_sub to the actual pool count and substitute steps6-7;
   ring arithmetic gives the stated second moment. No independence is assumed
   between the two gates of a same-tag representation.

No new maxHeartbeats/recursion limits, custom axioms, sorry or native_decide.
Retain every failed source/log as a text snapshot before repairing a tracked
probe. One Lake process at a time. Preserve the unrelated untracked Velu probe.
Run the all-source/axiom gate after final edits; no fresh checker pass without
an actual executable and successful run.

## Cost and falsification questions

Count every explicit pair subtotal, auxiliary shift test, surviving record,
compatible-tag join, deduplication and final check. Analyze streaming and
materializing all tags separately. Increasing k to offset a small filter
density does not make these representations free. Compare the four-color
construction against the ordinary explicit pair-sum join on the same input;
do not extrapolate this fixed-height accounting to all deep/adaptive trees.

If moment retention is favorable but the explicit construction grows with
the raw triple family, the next constructive target is a charged curve-specific
batch translated-filter query without enumerating every triple. That would
need its own literature review, representation and useful-output proof.

## Literature and source review before choosing this assembly

KB unavailable: no connector; inherited wrapper failure unchanged. Read
frozen candidate C and Wagner2002 primary author PDF sections2-3, especially
the actual scalar/XOR/subgroup join conditions and compatible filtering.
Source file /workspace/scratch/cover-transfer-literature/Wagner2002-full-author.pdf;
fresh text extraction /workspace/scratch/Wagner2002-C-review001.txt.
Read Howgrave-Graham/Joux's primary EUROCRYPT2010 slides9-14:
https://www.iacr.org/conferences/eurocrypt2010/talks/knapsacks.pdf . They
describe overlapping representations with explicit modular constraints;
those scalar filters are not supplied by a point's coordinate interval.
No historical complexity exponent is imported. A primary BCJ full-paper
mirror timed out; indexed excerpts alone are not a full algorithm review.
https://acm.math.spbu.ru/~sk1/download/papers/knapsack/knapsack-978-3-642-20465-4_21.pdf .
Read the pinned Mathlib UniformOn, Bernoulli, variance_sum_pi,
integral_comp_eval, Fintype product/counting and Point equivalence sources.
No novelty, cheap-generation or general lower-bound claim is made.
