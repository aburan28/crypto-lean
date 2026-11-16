# A bounded candidate sampler with useful-subset coverage

16 November 2026. Product-compatible pair isolation connects the existing
one-character elliptic finder to a bound on hitting any fixed useful subset.
The design returns logarithmically many checked candidates per round.
Eleven shared finite-count/colour laws and actual instances compile locally;
the sampling wrapper, recovery and complexity remain hand reasoning, with
no executable or measured sampler. The [diagram](pair-colour-isolation-20261116/flow.svg),
[PDF](pair-colour-isolation-20261116/report.pdf) and
[publication boundary](pair-colour-isolation-20261116/PUBLICATION.md) accompany the source. [pcc:unverified]

## Interface and input law

Keep two EXPLICIT indexed point-record lists of lengths N,M, an actual
prime-field curve/anchor and the one-character predicate from
[the earlier component](character-parity-20261116.md). Let S be the set of
all indexed passing pairs, g=|S|, and T any fixed useful subset of S.
Every record retains its original primitive coefficients, labels, support
and provenance; repeated point values remain distinct record indices.
The set T is fixed before the sampler's randomness. [pcc:unverified]

For N,M>0, use dyadic levels ell=1,...,L, where

    L=ceil(log2(2*N*M)).

A round returns at most L checked indexed pairs, including possible
duplicates across levels. For g>0 define theta=|T|/g. The hand coverage
bound is

    Pr[the round's candidate list intersects T] >= theta/8.

If a supplied useful predicate exactly recognizes T, inspect EVERY returned
candidate, accept only after its complete checks, and run at most q fresh
independent rounds. The miss bound is (1-theta/8)^q. Empty input returns an
empty list. When g=0 the list is empty, but the capped procedure supplies
no emptiness certificate. No theta bound for the original full relation
problem follows from isolation. [pcc:unverified]

## The product-compatible hash

At level ell choose independent uniform labels r_i,c_j in H=(F2)^ell for
EACH ORIGINAL row/column RECORD. Keep a pair exactly when

    h(i,j)=r_i+c_j=0.

Group rows by r_i and columns by c_j, and search matching-colour buckets.
For other finite additive colour groups, match r_i to -c_j. All buckets
partition the original explicit records, so

    sum_colours (number_of_rows + number_of_columns) = N+M.

Iterate occupied buckets only. Even if |H| exceeds the number of records,
there is no loop over |H| or over the original N*M pairs. Equal point
values may be assigned different colours, and all per-bucket polynomial
products/corrections retain their record multiplicities. [pcc:unverified]

The colour sample space is Omega=(I->H)*(J->H), an existing finite additive
group. The pair map h_e:Omega->+H is the sum of existing evaluation homs
composed with the two product projections. It is surjective. For two
distinct record pairs e,f, the paired hom (h_e,h_f):Omega->+H*H is also
surjective: if row IDs differ, assign their two row labels and all columns0;
otherwise distinctness forces different column IDs, which can be assigned
with all rows0. [pcc:unverified]

Existing equal-fiber cardinality then gives, with B=|H| and C=|Omega|,

    B * |{omega:h_e(omega)=0}| = C,
    B^2 * |{omega:h_e(omega)=h_f(omega)=0}| = C  (e!=f).

These are pairwise independence, not full independence of all edges.
In particular, four-cycle hash values can be dependent. The proof and
sampler use no stronger condition. The actual F2-vector and prime-field
point-sum graph endpoints apply the same shared count law. [pcc:unverified]

## Exact finite isolation count

For each edge e, let A_e be its zero-hash event. Its isolated part is

    U_e = A_e minus union_(f in S, f!=e) A_f.

The union removes ALL other passing pairs, including nonuseful ones.
Standard finite union bounds give

    |A_e| <= |U_e| + sum_(f in S, f!=e)|A_e intersect A_f|.

The U_e for different target edges are disjoint. Sum over e in T,
multiply by B^2 and apply the single/pair fiber scalings:

    |T|*C*B <= B^2*|union_(e in T)U_e| + |T|*(g-1)*C.

When B>=2g and B>0, positive-factor arithmetic yields the compiled endpoint

    |T|*C <= 2B*|union_(e in T)U_e|.

Uniform finite sampling therefore isolates a target edge with probability
at least |T|/(2B). There is a dyadic level with 2g<=B<4g because
1<=g<=N*M. At that level the probability is at least theta/8. The full
round tries that level even though g is unknown. No independence between
different level outcomes is needed for this single-level lower bound;
complete repeated rounds use fresh randomness. [pcc:unverified]

## Recovery needs singleton completeness, not uniform output

Inside each matching-colour bucket, execute the earlier direct scans for
input O,+/-anchor, coincidence and inverse pairs. If no direct case passes,
compute all row parities using column mask1, then scan one odd row and
check actual group addition. This deterministic procedure is sound and
recovers a pair whenever the bucket has exactly one passing pair. It can
miss a larger nonempty bucket when all row parities are even. [pcc:unverified]

At one level return the first checked pair recovered from any bucket, or
none. On the event that a target edge is the unique retained passing edge,
all other buckets contain no passing pair and cannot return a checked pair
first. Its own bucket must return that target edge. Behaviour on larger
graphs may be biased; it does not invalidate this event inclusion. Thus
the finite isolated-target probability transfers to list coverage.
[pcc:unverified]

Do not return a global direct-case witness before hashing: that would
bypass the coverage argument. Shared preprocessing may prepare coordinates,
point keys and immutable record references, but direct returns happen only
inside selected buckets. Do not stop the all-level wrapper at an arbitrary
nonuseful candidate. Check the useful predicate and continue if it fails.
Adaptive target subsets chosen after seeing colours are outside this bound.

## Charged cap and what it enables

The existing row-parity routine has a hand quasilinear cost per explicit
bucket, including repeated-root Taylor stripping and all exceptional
corrections. Summing over matching buckets costs O~(N+M) per level. A full
round costs O~(L*(N+M)) field operations, plus O((N+M)*L^2) random bits and
sorting/metadata work. If V bounds complete extraction, label, coefficient
and group/scalar verification per candidate, q rounds cost

    O~(q*L*(N+M)) field operations + O(q*L*V) validation,
    O(q*(N+M)*L^2) random bits; at most q*L candidates.

Include bit arithmetic and provenance storage in the actual input length.
Buckets store record references; no large primitive vector is copied for
free. An implicit Cartesian family is not an explicit input list. These
are symbolic accounting bounds, not timings or an implemented kernel.
[pcc:unverified]

A justified theta>=2^(-O(m log(m+1))) would allow a correspondingly bounded
q while retaining the earlier fast-selector cost target. This construction
supplies the transfer from an actual useful fraction to a capped candidate
list; it does not supply that fraction, a cheap implicit-family generator,
or a simultaneous-gate oracle. Direct random-pair rejection remains the
baseline for dense gates. No speedup is claimed from coverage alone.
[pcc:unverified]

## Proof map

The [prospective plan](pair-colour-isolation-20261116-plan.md) records the
six fields, exact inherited laws, proof chain, controls and failed attempts.
New owner interfaces:

| Interface | Kind / owner | Inherited structure |
|---|---|---|
| single_cover_count | Generic law, FiniteIsolation | sdiff/intersection card and finite union bound |
| target_events_disjoint | Generic law, FiniteIsolation | Actual isolated event membership |
| target_union_count | Generic law, FiniteIsolation | Disjoint card_biUnion, finite sums |
| scaled_target_isolation | Generic law, FiniteIsolation | Single/pair scaling hypotheses |
| half_scaled_target_isolation | Endpoint, FiniteIsolation | Previous count and positive-factor arithmetic |
| edgeColour_apply | Instance obligation, PairColourIsolation | Eval/projection/add hom definitions |
| edgeColour_surjective; two_edge_surjective | Instance obligations, PairColourIsolation | Explicit independent record-label assignments |
| single_fibre_scaled; pair_fibre_scaled | Endpoints, PairColourIsolation | Existing fiber_card_mul unchanged |
| target_colour_count | Endpoint, PairColourIsolation | Generic finite isolation law and actual fibers |

There are eleven named theorems and one hom definition. Sourcea39b093
contains all owned laws and the actual finite-colour/prime-field graph
probes. Canonical gate001 reports247 audited theorems with0 failing and0 trusted-
native exceptions; all eleven actual named compiler axiom prints use only
allowed standard axioms. Completion receipts are preserved in PUBLICATION. The dyadic probability,
singleton recovery, bounded-list wrapper and complexity are hand arguments.
No signed independent verification or fresh checker is asserted.
[pcc:unverified]

## Literature and comparison of approaches

KB tools unavailable; bounded source/Mathlib plus primary fallback. No
novelty conclusion follows from that gap.

- Valiant--Vazirani, *NP is as easy as detecting unique solutions* (1986),
  [primary paper](https://ics.uci.edu/~vazirani/ValVaz.pdf), proof pp87--90:
  witness isolation by random GF2 constraints. The finite target-isolation
  argument here is standard hashing/union-bound reasoning. SAT hardness
  is not an elliptic lower bound.
- Addanki--McGregor--Musco, *Non-Adaptive Edge Counting and Sampling via
  Bipartite Independent Set Queries* (2022), [full primary version](https://arxiv.org/pdf/2207.02817),
  Algorithm6/Theorem38; proceedings Theorem2/7: a stronger near-uniform
  edge sampler uses polylogarithmically many EXACT BIS queries. Read the
  query model, sampler and proof context. This is relevant prior art;
  no total elliptic-runtime theorem is imported. Instantiating every query,
  input construction and cumulative one-sided-error transfer is separate.
- Dumas--Pernet--Saunders, *On finding multiplicities of characteristic
  polynomial factors of black-box matrices*, [primary paper](https://arxiv.org/pdf/0901.4747),
  trace discussion: n pure black-box matvecs compute trace; structured
  representations can be faster. This is not an impossibility theorem
  for a structured elliptic joint-gate routine. [pcc:unverified]
- Existing PR23 report and pinned Mathlib finite-cardinality, additive-hom,
  finite-sum/union laws listed in the prospective plan. The generic
  count/fiber objects are semantic finite groups/events, not duplicated
  curve laws.

Multiple individual or subset-XOR gate parities still do not determine AND
parity. This sampler can verify extra gates on its bounded candidates, with
the resulting actual useful fraction charged explicitly. It does not turn
them into a cheap joint block query. A useful-subset fraction cannot be
inferred from representation multiplicity or assumed output uniformity.
[pcc:unverified]

The user's complete classical subexponential prime-field ECDLP criterion
remains unmet. New numerical/native cases, paid jobs and qualification
runs: none. Old63 claim subjects and the eight-row ledger prefix remain
preserved; consumer frozen histories stay separate. No evaluated native
identity.certificate/v1 was issued in this execution scope. The diagram
and PDF describe the design; there is no performance data to plot and no
benchmark, leaderboard or canonical performance-graph change.
[pcc:unverified]
