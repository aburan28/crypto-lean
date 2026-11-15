# Marker-rank implementation map

The prospective plan and inherited-law floor are frozen by
PCC-20261115-9ea735, an unverified pre-source statement. This separate map
records implementation interfaces without changing those pinned subjects.

| Statement | Kind | Owner | Structure / hypotheses |
|---|---|---|---|
| minimum_spec | law/interface | Group.RankThreshold | LinearOrder K, positive pool size |
| poolSwap_apply | law/interface | Group.RankThreshold | AddGroup G, actual ordered pools |
| success_iff | law/interface | Group.RankThreshold | same, key into LinearOrder |
| success_tag_iff | law | Group.RankThreshold | minimum attainment/bounds |
| success_swap_iff | law | Group.RankThreshold | translation cancellation |
| success_or_swap | law | Group.RankThreshold | le_total after reversal |
| raw_card_le_twice_success | endpoint | Group.RankThreshold | finite G, card_union_le and subtype equivalence |
| right_shift_eq_neg_left | law | Group.ShiftRepresentations | AddCommGroup, U+V=0 |
| paired success endpoint | endpoint | Group.RankThreshold | key negation symmetry, opposite subtotals |
| actual prime-field assembly | instance/endpoint | receipt probe | existing nonsingular-point equivalence and xRep_neg |

## Opening composites once

The new cached minimum has no existing interface under its new name.
`minimum_spec` alone opens it, to apply Mathlib min'_le and min'_mem to
the finite image. The image chooses a value; raw pools remain function
spaces with their complete multiplicities. Consumers use its two projections.
`poolSwap_apply` alone opens the named composition of existing equivalences;
`success_iff` alone opens the new comparison predicate. There is no existing
lemma about those names before their introduction. No other proof unfolds
these composites. The paired predicate receives its own single rfl interface.

## Chain used by the next consumers

1. The minimum comparison is equivalent to an actual adjusted tag below
   every marker, by attainment and the lower-bound half of minimum_spec.
2. poolSwap is the already checked pi/prod/addLeft composition. Its adjusted
   second pool equals the old marker pool by add/neg cancellation.
3. success on the swapped state is the reversed minimum comparison.
4. le_total covers the raw pool space with success and its swap preimage.
5. subtypeEquivOfSubtype and Nat.card_congr equate their cardinalities.
6. Finset.card_union_le gives the factor-two raw cardinality endpoint.
7. The shared right-shift identity and key symmetry identify both child
   tests with the same accepted tag. No independence of the child tests.

No run-time claim follows from the counting proof. Swap is an analysis
equivalence only, not an input sampler or a planted closing witness.

