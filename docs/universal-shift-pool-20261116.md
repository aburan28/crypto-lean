# A shared shift pool for adaptive two-gate retention

16 November 2026. This component replaces an assumption about selected-output
uniformity with a simultaneous finite-family guarantee. Nine new generic
finite-support/pool laws and actual prime-field semantic probes compile;
the character-sum estimates and real exponential cap below are hand analysis.
The [prospective plan](universal-shift-pool-20261116-plan.md),
[editable diagram](universal-shift-pool-20261116/flow.dot),
[PDF](universal-shift-pool-20261116/report.pdf) and
[publication scope](universal-shift-pool-20261116/PUBLICATION.md) accompany it.
No executable selector or measured cost is supplied. [pcc:unverified]

## Gate and exact domain

Let E/Fp be an elliptic curve, p>3, and H a subgroup of prime order r.
Choose k anchors T_j in H with distinct abscissas, all nonzero and not
two-torsion, and require 2k<r. Public anchors T_j=jG, 1<=j<=k, satisfy these
conditions for a public generator G. Let chi be the quadratic character,
including chi(0)=0, and define

    kappa_j(O)=1; kappa_j(P)=chi(x(P)-x(T_j)) otherwise;
    D={P in H: every kappa_j(P)=+1};
    C_W={P in D: W-P in D}.

Then D=-D. The existing TranslatedIntersections.both_gates_iff gives

    (U+t in D and V-t in D) iff U+t in C_(U+V).

Neither the gate nor the pool changes original record indices, primitive
coefficients, support or provenance. A tag t=sG has known scalar s, so its
opposite additions cancel without altering the original Q-label coefficients.
Retain s and its placement explicitly. [pcc:unverified]

## Why the mixed Kummer terms remain nontrivial

For I a subset of anchors, put f_I(P)=product_(j in I)(x(P)-x(T_j)).
Its odd-valuation support is S_I={+T_j,-T_j:j in I}; this set has
2|I| points and group sum zero. The pole at O has even order and leading
unit1 for the usual local parameter. For W!=O, the mixed function

    f_I(P) f_J(W-P)

has odd support the symmetric difference of S_I and W-S_J. If this support
were empty and one subset nonempty, equality S_I=W-S_J would force both
subsets nonempty and the same positive cardinality n<=2k. Reflection sums
give 0=n W-0. But W has order r and 0<n<r, a contradiction. Empty I or J
causes no exception: a nonempty support cannot equal the empty support.
The shared TranslatedSupports laws formalize the generic reflection/order
argument; no curve-specific group proof is repeated. [pcc:unverified]

Perret1991 proposition3.1 gives tame quadratic conductor the noncanceled
odd support, of degree at most 2(|I|+|J|). It also explains modified values
at even zeros and poles. Kohel--Shparlinski section2 propositions1/2 give
the finite-order character L-function square-root estimate, and section3
constructs the unramified group-character twist through the Lang isogeny.
An unramified twist cannot remove nonzero ramification. Hence the complete
mixed-character sum, including a group-character twist, has absolute value
at most 2(|I|+|J|)sqrt(p). This is a hand application of the cited framework,
not a Lean theorem or an invocation of their additive theorem1 as a
multiplicative theorem. [pcc:unverified]

To restrict to H, average twists over its annihilator in the dual of E(Fp).
The subgroup indicator is the normalized sum of those characters. The
normalization cancels their number, so the same upper bound holds for the
subgroup sum, independent of its index. The ramification argument is what
excludes a geometrically constant exception after twisting. [pcc:unverified]

## Canceled zeros and the density error

Ordinary gate products cannot simply be identified with a modified Artin
character at a common even-order zero: the former can be0 while the latter
is unramified and nonzero. Remove the WHOLE fixed set

    Z={+/-T_j:all j} union {W+/-T_j:all j},  |Z|<=4k,

before expanding the two gate indicators. Off Z the original products and
modified local characters agree, including even poles at O or W with the
specified local units. At a point of Z the actual conjunction is false.
The normalized sum of all restricted-term corrections is at most |Z|:
there are 4^k terms, each normalized by 4^k. There is no exponential
correction factor left over. [pcc:unverified]

The trivial term contributes r. The sum of conductor bounds is

    (1/4^k) sum_(I,J) 2(|I|+|J|) sqrt(p) = 2k sqrt(p).

Consequently the hand estimates are

    abs(|D|-r/2^k) <= k sqrt(p)+2k;
    abs(|C_W|-r/4^k) <= 2k sqrt(p)+4k, for W!=O.

The one-gate estimate uses the same argument with just 2k possible zero
points. For W=O use C_O=D, by symmetry, instead of the mixed-support
noncancellation proof. For k=0 all gates accept and no ramification
argument is needed. A sufficient condition for the uniform bound

    |C_W|/r >= 1/(2*4^k), for EVERY W in H,

is r>=2*4^k*(2k sqrt(p)+4k). This is an explicit restriction: it is not
assumed valid for every prime-order subgroup or every growing k.
For large subgroups r comparable to p and 2^k polynomial in log p it holds
asymptotically. No numerical panel was run. [pcc:unverified]

## One pool, all pairs, including adaptive reuse

For any ordered pair (U,V), let A_(U,V) be the set of good shifts t.
Translation U+t is a bijection, so |A_(U,V)|=|C_(U+V)|. Sample a pool of
Q independent uniform points in H, allowing repeated tags. More generally,
for ANY finite family of good sets A_i of size at least a, the exact finite
statements compiled in UniversalPools are

    number(pools missing A_i) = (r-|A_i|)^Q;
    number(pools missing some A_i) <= |I|*(r-a)^Q;
    |I|*(r-a)^Q < r^Q implies some pool hits every A_i.

The fixed-event equality applies the inherited subtype-function equivalence
and cardinality laws. The universal inequality applies the inherited finite
union bound. Empty demand families and Q=0 are covered by the statements;
the strict condition cannot pretend a zero-length pool hits a nonempty
demand. Repeated pool tags are retained as distinct coordinates. [pcc:unverified]

For I=H*H, divide by r^Q and use 1-x<=exp(-x). Under the density condition,

    Pr[some pair misses every tag] <= r^2 exp(-Q/(2*4^k)).

For 0<epsilon<1 it suffices to choose the integer cap

    Q=ceil(2*4^k*(2 ln r+ln(1/epsilon))).

The good-pool event quantifies over ALL pairs in H, before any adaptive
choices. On that event, any adaptively chosen sequence of pairs may reuse
the pool: each pair has a good tag. This is stronger than asserting a
bound for a fixed sequence and then silently conditioning it on the pool.
The simultaneous probability and real logarithmic cap are hand consequences
of the compiled finite count. [pcc:unverified]

## What this buys, and the next extraction test

Generate each tag as sG using an independent exactly uniform scalar s in
Z/rZ; use capped rejection if an implementation requires a bit-only random
source, and charge its additional failure budget. Store Q scalars/points.
For an already known pair, scan at most Q tags and at most 2k quadratic
characters per tag. Include scalar multiplication, group addition, character
exponentiation, bit costs and all failed tags. For polynomial 2^k in log p,
Q is polynomial in log p and log(1/epsilon). This accounting is hand
analysis; no executable or timing comparison is supplied. [pcc:unverified]

This result preserves decompositions. It does not enumerate an implicit
pair family, locate an original catalog tuple, or establish a useful
nonzero-relation fraction. Indeed, when every pair has a tag, existentially
eliminating that tag rejects no original pair at all. Building a tree by
splitting known group labels can still produce only the trivial conserved
coefficient relation. The earlier tree result applies to retention of a
known tuple, and the pair-colour result applies to explicit indexed lists;
neither silently provides hidden-tuple extraction here. [pcc:unverified]

The next discriminating direction is an arithmetic-height extractor using
the actual homogenized S3 equations, with every denominator variable and
field-coefficient height charged. A candidate must produce enough independent
equations to recover original support under a fixed total frontier cap;
neither a single short lattice row nor low map degree suffices. Read the
primary small-root solver hypotheses before writing such a solver claim.

## Evidence and source boundaries

Nine new named laws: TranslatedSupports sum_reflection,
centered_reflection_nsmul, centered_reflection_ne, sum_symmetric_union;
UniversalPools fixed_miss_count, mem_badPools, miss_union_bound,
universal_miss_bound, exists_universal_pool. The actual subgroup and
quadratic-character gate probes apply them unchanged. No analytic axiom,
sorry, native_decide, proof-limit override or inventory exception was added.
The final canonical gate exits0 with258 audited theorems,0 failing and0
trusted-native exceptions; all nine named compiler prints use only standard
allowed axioms. Records are indexed in PUBLICATION.
No evaluated native identity certificate is issued. [pcc:unverified]

Sources checked (KB): tools unavailable; bounded exact owner/Mathlib search
and the primary sources indexed in source-review001.json were used. Perret's
Acta primary pp284--288 supplies the regularity/conductor/local-value details;
the conference exposition alone was not treated as a complete proof. No
novelty, empirical speed, hosted CI pass or complete ECDLP algorithm is claimed.
