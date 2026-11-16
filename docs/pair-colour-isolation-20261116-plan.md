# Pair-colour isolation: prospective useful-subset sampler

16 November 2026. Continue the complete classical prime-field ECDLP goal;
the criterion is unchanged. This component asks for a distributional
interface on the explicit-list one-character graph, not a many-gate oracle.
Only mathematical/compiler work; no numerical/native cases, paid jobs or
qualification runs. Preserve all63 older claim subjects and the eight-row
ledger prefix. Do not touch the unrelated Velu probe or consumer conflicts.

## Question, prediction and accounting

Can a singleton-complete finder, however biased on larger graphs, cover
every useful subset of the passing graph with an explicit probability floor?
Prediction: yes by standard pairwise hash isolation, choosing a product-
compatible hash so its zero fiber can be searched without constructing pairs.

For record-index sets I,J, choose independent uniform colours r_i,c_j in
H=(F2)^ell and retain pairs r_i+c_j=0. Each vertex belongs to one colour
bucket. Matching buckets partition ALL explicit records; their total input
length is N+M even when 2^ell is huge. Iterate only occupied buckets. Use
the one-character direct-case scans and all-row parity with column mask1,
returning an actual checked pair from the first successful bucket. If the
retained graph has exactly one passing edge, this deterministic routine
must return it. Otherwise it may return another valid edge or none.

Let g>0 be the number of passing indexed pairs and W any fixed subset of
them, independent of colours. For B=|H|, pairwise independence gives for
each e in W:

    Pr[e is the unique retained passing pair]
       >= 1/B-(g-1)/B^2.

These events are disjoint. When 2g<=B<4g, their union has probability at
least |W|/(8g). Pick ell uniformly from a set of L=O(log(NM+2)) levels
containing such a B. One output then belongs to W with probability at
least |W|/(8gL), without assuming the finder's output is uniform. A wrapper
checking a supplied useful predicate repeats under a fixed cap; its bound
depends on the actual ratio theta=|W|/g. No theta for elliptic relations or
many-gate conjunction is assumed or supplied by isolation. [pcc:unverified]

Count point preparation, random record colours, occupied-bucket sorting,
the sum of per-bucket direct/parity work, final original-index recovery and
predicate checks. Hand target: quasilinear per sample, up to the existing
one-character polynomial arithmetic/logarithms. This is a design, not an
implemented or measured sampler. Direct uniform pair rejection remains
the comparison for dense gates; no speedup follows solely from coverage.

## Literature first

KB tools unavailable. Bounded repository/Mathlib plus primary fallback:

- Valiant--Vazirani1986, https://ics.uci.edu/~vazirani/ValVaz.pdf,
  proof pp87--90. Standard isolation using GF2 constraints; no novelty claim.
  The per-target pairwise union-bound variant here is an explicit finite
  count, not a re-interpretation of SAT hardness as an elliptic lower bound.
- Addanki--McGregor--Musco2022, https://arxiv.org/abs/2207.02817,
  proceedings Theorem2/7 and section4: stronger near-uniform edge sampling
  using polylogarithmically many exact BIS queries. Full sampler details
  require the full version. Its query count is not total elliptic cost;
  exact/noisy-BIS error and pointwise distribution transfer must be charged.
- Dumas--Pernet--Saunders2009, https://arxiv.org/pdf/0901.4747,
  trace discussion: pure black-box trace uses n matvecs; structured cases
  can be faster. This does not prove the elliptic joint oracle impossible.
- Existing CharacterCarry/ProjectiveProducts/BilinearSketch, source PR23:
  actual one-character row parities and raw-mask counts. Mathlib finite
  products/cardinality, additive hom evaluation/product and finite union
  bounds. No Valiant--Vazirani declaration found in bounded probability/
  combinatorics search. Search absence is not a novelty result.

## Six fields before the first Lean edit

1. Structures: finite additive commutative groups and homomorphisms;
   function/product additive groups; Finset events and finite record IDs.
2. Existing laws: Pi.evalAddMonoidHom, AddMonoidHom.fst/snd/comp/add/prod;
   ShortlistCompletion.fiber_card_mul; Fintype.card_prod and subtype card;
   Finset.card_union_le, card_biUnion_le, card_biUnion for disjoint events,
   card_sdiff/card_inter and finite sums. Apply unchanged.
3. Objects: Omega=(I->H)*(J->H), edge hom omega -> r_i+c_j,
   its paired hom for distinct indexed edges; event A_e is its zero fiber.
   Abstract finite event sets own the isolation count, not a curve-specific
   experiment or a new hash syntax.
4. Assembly floor: type-check the existing hom compositions/evaluation and
   inherited fiber scaling over generic groups; then H=Fin ell->ZMod2.
   Compile the finite cover/disjoint-union argument before a new owner law.
5. Missing only: surjectivity glue for one/two distinct edge-colour maps;
   generic finite target-isolation inequality and its scaled fiber endpoint.
   These belong shared owners first. Actual elliptic point records use
   their original index sets unchanged; no repeated group/curve argument.
6. Inheritance table:

| Operation | Existing floor | Missing glue |
|---|---|---|
| Hash a pair | eval homs + product projections + addition | composition only |
| Independent one/two edge outputs | fiber_card_mul | explicit surjective assignments |
| Exclude collisions | card_union_le, card_biUnion_le | event cover |
| Sum isolated target events | disjoint card_biUnion | uniqueness disjointness |
| Hash probability | uniform finite-card ratio | scaled-count arithmetic |
| Actual gated pair recovery | PR23 direct/parity algorithm | singleton-complete wrapper, hand |

Proof chain for counts: A_e is covered by its isolated part plus the union
of A_e intersect A_f for f!=e. Apply finite-card union bounds unchanged.
Sum over target edges; isolated parts are pairwise disjoint. Multiply by
B^2 and substitute existing single/pair zero-fiber scalings. Thus

    |W|*|Omega|*B
      <= B^2*|isolated target outcomes| + |W|*(g-1)*|Omega|.

If B>=2g and B>0, cancel to obtain

    |W|*|Omega| <= 2B*|isolated target outcomes|.

Two-edge surjectivity chain: if row IDs differ, assign their two row
colours arbitrarily and all columns0. If row IDs agree, distinctness forces
the column IDs to differ; assign their two column colours and all rows0.
No curve, point-distribution or selected-output hypothesis enters this law.

## Controls and completion

Empty target subset; one passing pair; repeated point values with distinct
record IDs; same-row/same-column/disjoint edge pairs; cycles (hashes are
pairwise, not fully independent); all-even row parities; many unoccupied
colours; adaptive useful predicates are outside the fixed-W statement.
Probes are symbolic compiler assemblies, not numerical curve cases.

One Lake process at a time, preserve failures and source snapshots, no
proof-limit/trust/inventory/linter changes. Final canonical audit and every
new named axiom print before publication. Record the hand sampling bound
separately from compiled finite laws, and retain the original full-algorithm
criterion. Continue actual joint-gate construction after this component.


Recovery clarification before endpoint assembly: point/key preprocessing may
be shared, but no global direct-case witness is returned before hashing.
Each selected matching-colour bucket executes its own direct scans, then
all-row parity with column mask1. On a unique retained edge, one of those
paths recovers it. All other buckets are empty of passing edges and cannot
return a checked pair first. This singleton-completeness argument is hand
algorithm reasoning; it is not a claim of an executable implementation.


Primary wrapper refinement: retain at most one checked pair from EVERY
dyadic level rather than selecting one random level. A round returns at
most L candidates and costs the sum of L near-linear bucket searches. The
correct unknown scale is present, so any fixed W is hit with probability
at least theta/8 per round. Checking all candidates for a fixed useful
predicate and repeating q independent complete rounds gives miss at most
(1-theta/8)^q. Each level uses fresh independent vertex-record colours;
charge O((N+M)L^2) random bits per round and all candidate validation.
No independence between hypothetical selected outputs is assumed. The
one-random-level/one-output interface remains valid with its extra L loss.
Both are hand algorithm/probability applications of the compiled count.
