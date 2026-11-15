# Finite-group partite coverage endpoint

Prospective A1 at crypto983490ac55: prove coverage over existing finite
additive commutative groups, with assignments on a partite record grid. The
first source builds tuple-sum/joint-sum additive homomorphisms, proves their
surjectivity by two unique coordinates and instantiates existing kernel/
range cardinality laws. The full second-moment/support endpoint remains a
required continuation; these counts alone must not be presented as that
completed theorem. No numerical case, relation selector or complexity claim.

Existing sources checked before implementation: Mathlib GroupTheory.Index
AddSubgroup.card_ker_mul_card_of_surjective, finite sums/Pi.single and finite
Cauchy--Schwarz in Algebra.Order.BigOperators.Ring.Finset. KB unavailable
in the consumer runtime; APS2018 sections3--3.2 and exact prior/internal
source identities remain in its SCOPE.md/checks.

Preserve first-build diagnostics, theorem statements and canonical source/
axiom gate receipts. Standard foundations only; no proof-limit override,
custom axiom or native_decide. Label/curve-cleanliness/program bounds remain
separate from this finite-group probability claim.

## Build progression

- 62cac65/build001 failed only because Lean could not infer the codomain of
  Pi.single in a `change`. 248ad81 specifies that existing function type;
  build002 passes with unchanged mathematical statements.
- 4c6dd9a/build003 passes actual single/joint event counts, the first moment,
  and finite Cauchy--Schwarz on the support. The second moment and instantiated
  coverage endpoint are still required. A declaration probe preserved two
  unknown guessed convenience names; the existing sum_erase_add and
  sum_mul_sum statements were read instead. No limits were changed.
- f5b4cbb/build004 proves the diagonal/off-diagonal row and the support's
  existential characterization, but fails when a global square expansion also
  rewrites the normalizing factor before the row rewrite. Restrict the
  expansion to relationCount's square; preserve all theorem statements.
- 3792669/build005 checks both exact moments and every coverage proof step
  except the final equality-up-to-commutativity: a broad rw commutes both
  products. Use a local `simpa only [mul_comm]` at that last step, with the
  same endpoint and hypotheses.
