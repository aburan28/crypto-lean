# Marker-rank thresholds: prospective continuation of candidate C

2026-11-15. Before the first Lean edit of this new family. The prior
auxiliary-shift plan/floor are pinned by unverified PCC-20261115-102ac7;
do not edit those files. Its raw fixed-filter moment endpoints remain open.
The first provenance/two-gate block builds at4230a21. This new family asks
for a constructive random threshold and a direct survival bound; it does
not silently discharge the older moment task or the complete-algorithm criterion.
No native numerical, paid or qualification execution is authorized or planned.

## Proposed rule and exact target

Use a symmetric, totally ordered point key kappa, such as an ordered encoding
of the normalized x representative. Draw b independent uniform marker points
M_i and an independent b-point auxiliary shift pool T_j. For a fixed U, set

    threshold = min_i kappa(M_i),
    accept j iff kappa(U+T_j) <= threshold.

Precompute the marker minimum once. Every comparison is between actual point
keys. Markers are independent selector coins; their generation/read costs are
charged. If generated as public random scalar multiples of the subgroup
generator, the sampler law and O(b*log r) group-operation accounting have
their own hand scope. No private original labels are inspected. Auxiliary
primitive coefficients remain explicit and cancel only for compatible tags.

For U+V=0 and kappa(-P)=kappa(P), a tag passing the left test also passes
the right test on V-T_j. The proposed exact finite endpoint is

    Nat.card ((Fin b -> G) x (Fin b -> G))
      <= 2 * Nat.card {pools // some compatible tag passes both gates},

for b>0 under the actual raw independent uniform pool model. Ties are retained.
No uniformity of kappa's image, distinctness of sampled keys or field-coordinate
equidistribution is assumed. The target is a survival statement for a fixed
original valid relation, not a cheap algorithm for finding that relation.

## Six-field instance statement

1. Structure above: existing additive groups, function/product equivalences,
   Finset finite minima over a LinearOrder, finite subtype cardinality and
   Finset.card_union_le. Actual objects are ordered arrays of group points.
2. Existing laws used as stated: Equiv.addLeft and its inverse;
   Equiv.piCongrRight, Equiv.prodCongr, Equiv.prodComm; Finset.min',
   min'_mem/min'_le; totality of <=; Equiv.subtypeEquivOfSubtype;
   Nat.card_congr and finite cardinality identities. No generic sampling,
   minimum or union-cardinality law is re-proved for a curve.
3. Objects as instances: the pool state is (M,T) in (Fin b->G)^2, with full
   multiplicities. The adjusted pool is U+T pointwise. Use the existing
   equivalences to construct poolSwap_U(M,T)=(U+T,-U+M). The finite image
   used to compute a minimum does not deduplicate raw sample states.
4. Assembly probe: check these existing equivalences/minimum/cardinality
   operations on a generic additive group and actual finite ordered arrays.
   Repeat the group/key assembly at ZMod p Weierstrass points/subgroups,
   using the exact finite-point inheritance/context already checked by
   AuxiliaryShift20261115/FloorProbe.lean. A final probe must apply the new
   shared endpoint unchanged at those objects. Keep derived NeZero p and
   required local finite instances explicit; do not add mathematical hypotheses.
5. Missing components only: cached minimum interface; pool-swap application
   interface; event reversal/cover; finite success-cardinality bound; and
   the actual two-gate reading under zero-sum and negation-invariant key.
   Extract any needed generic right_shift_eq_neg_left law in its existing
   owning ShiftRepresentations module before the rank consumer. The older
   fixed-filter moments and density/cost analysis are separate obligations.
6. Inheritance table:

| Operation | Inherited law | New work |
|---|---|---|
| Ordered point pools | Fin b -> G, product | none |
| Adjust by U and invert | Equiv.addLeft U | pointwise composition |
| Swap adjusted and marker pools | existing pi/prod equivalences | named composition interface |
| Compute the marker minimum | Finset.min' | image/nonempty interface |
| Two opposite comparisons cover | le_total | rewrite by swap interface |
| Preimage success has same count | subtypeEquivOfSubtype, Nat.card_congr | endpoint |
| Whole space <= sum of two events | card_union_le | endpoint |
| Paired gates agree on a valid relation | existing group-shift identity + kappa negation | consumer interface |
| Actual symmetric point key | Mathlib Point.xRep_neg | instance |
| Actual finite point subgroup | nonsingularPointEquiv, Finite.of_equiv | instance |

## Proof chain before code

1. minAdjusted <= minMarker defines the one-sided success event. Existing
   minimum attainment/bounds identify it with an actual accepted tag.
2. The inherited pointwise translation and product swap give a bijection
   poolSwap(M,T)=(U+T,-U+M).
3. On the swapped state, the adjusted pool is M and the marker pool is U+T,
   by group cancellation. Its event is the reverse comparison.
4. Totality gives success(pools) OR success(poolSwap pools), including ties.
5. The two finite event sets cover the raw sample space. Their cardinalities
   are equal by the existing subtype equivalence. Apply card_union_le.
6. Under U+V=0 and kappa negation invariance, replace the second child key
   by the first. Thus the same event is the actual compatible two-gate event.

No proof-limit override, custom axiom, sorry or native_decide. Commit the
floor source/log before new shared laws. Keep failed sources/logs with fresh
paths; one Lake process at a time. The final all-source/axiom audit and actual
instance assembly remain required. The old unrelated Velu probe stays untracked.

## Selectivity, construction and limits to check separately

With key fibers of size at most2, exchangeability/tie counting suggests

    1/(b+1) <= E[filter density] <= 1/(b+1) + b/r.

This is a prospective hand bound, not part of the initial checked target.
Do not transfer continuous order-statistic formulas to finite fields without
handling ties. For a concrete key include infinity correctly; raw xRep0 alone
can collide with the infinity representative, unlike the full normalized key.

Charge b markers, b shifts, key computations, the minimum, every tested
translated subtotal, provenance and output checks. Enumerating two b^2-sized
partial-sum families against b shifts still tests O(b^3) states. Direct
survival does not pay that cost. A new constructive question is a charged
coordinate-aware batch translated-filter query with output-sensitive work.
No such query implementation/bound is supplied by this plan.

Do not multiply a one-join survival bound over internal nodes without their
own opposite-sum and independence contracts: a global zero relation does
not make every internal subtotal zero. Generic group operations plus an
ordered key alone are not a subexponential complexity argument.

## Prior review

KB unavailable; no connector and no changed fallback capability. Bounded
repository review checked the frozen A/B/C plan and earlier interval-join
assessment; no novelty assertion follows from that search. Read current
Mathlib finite minimum, equivalence and cardinality sources. Read Yen-Chi
Chen's primary UW lecture9, https://faculty.washington.edu/yenchic/20A_stat512/Lec9_Order.html :
its density/order-statistic formulas assume a continuous distribution and
almost-surely distinct values, so those formulas are not imported here.
The proposed finite swap proof explicitly permits ties. A Chicago L15
search hit did not contain the cited order-statistics section in the actual
document and is excluded; L16 was inaccessible. Wagner's primary scalar
filter conditions remain as recorded in the prior C plan. No borrowed
algorithmic exponent, cheap-generation claim or detailed novelty audit.
