# Bounded incidence and separated target-row blocks

Consumer: isogeny-labs/crypto PR5071, fixed-shape-incidence-v1. This task is
generic finite counting and field-matrix algebra; no curve arithmetic, root
oracle, sampling theorem or attack-cost theorem is supplied. [pcc:unverified]

## Instance gate before source

1. Structure above: Mathlib Finset/Fintype, finite products/unions, Matrix
   mulVec/vecMul/dotProduct over a field. No replacement arithmetic types.
2. Laws used as stated: Finset.card_biUnion_le, Finset.card_product,
   Finset.sum_le_sum, finite sum interchange, matrix-vector associativity.
   The missing consumer-facing laws are finite bounded-incidence pair counts
   and annihilation of tags constant on separated row blocks. They live here.
3. Objects: a column-to-target family of finite sets; a field matrix whose
   columns have a block owner, with a hidden valuation of its columns and a
   nonzero target value for each block. Hidden valuations occur in proofs,
   never as query inputs.
4. Assembly probe: instantiate union cardinality and matrix associativity
   with variable contracts, then finite nonvacuous count/matrix examples.
   Original Curve25519 group/map/scalar representation is a missing bridge.
5. Missing components: the generic laws below; consumer original-map
   incidence and uniform private-tag sampling bridges remain outside this PR.
6. Inheritance: unions/products/counts use Mathlib directly; field zero-product
   cancellation and matrix associativity are inherited, not native checks.

## Dependencies, statements and proof chain

| Statement | Kind/owner | Dependencies and sketch |
| --- | --- | --- |
| covered cardinality | law, Combinatorics.BoundedIncidence | union <= sum cardinalities <= number of columns times degree |
| ordered sharing pairs | law, same | union of fibre Cartesian squares <= sum of their squared cardinalities |
| block projection image | law, same | mask a hidden column valuation by its owner; support mask and row valuation give target times block indicator |
| separated-block kernel tags | law, same | zero left product paired with each projected valuation forces zero coefficient sum in each block; sum those with any block tags |

No theorem duplicates existing LargePrimeGraph singleton peeling. Its current
main source was read. SingleRelation mixed-label fibre and recovery already
exist and will be imported by the consumer when needed. [pcc:unverified]

## Fidelity and acceptance

Quantifiers range over arbitrary finite sets/matrices; bounds are natural
counts, not probability divisions. Empty sets are allowed; block target
values must be nonzero for cancellation. A zero target is handled separately
in the consumer. Column ownership excludes inter-block sharing. No hypothesis
will assert the desired tag conclusion. Nonvacuous examples must demonstrate
a permitted matrix and the effect of dropping the nonzero-target contract.
Use unchanged Lean4.35.0/Mathlib cfc55fc5, no new limits/trusted-native holes.
Build focused modules and inspect actual axioms; retain failed sources/logs.
Read the primary Diem large-prime/private-label discussion; classical union
and matrix identities have no novelty claim. KB unavailable (no loaded tool,
previous wrapper127), so no theorem-search completeness is inferred.
[pcc:unverified]
