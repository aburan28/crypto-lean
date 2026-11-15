# Finite-group partite coverage endpoint

The full finite-group endpoint is checked at source
2e4b08b719452f49bfef91e5c31329f2e251b445. Build006 and the canonical
repository-wide source/axiom gate pass: 134 audited theorems, 0 failures,
0 trusted native exceptions. Complete receipts and all six build logs are in
`docs/receipts/partite-coverage-20261115/`; the source inventory includes
PartiteCoverage. The new module contributes 16 audited declarations including
two definition-equation declarations. Only the standard propext,
Classical.choice and Quot.sound foundations occur. Hosted CI is separate.

For a finite additive commutative group G of cardinality r, m,b>0, set
L=b^m and N=r^(m*b). The endpoint `CryptoLean.PartiteCoverage.coverage_count`
states the exact integer inequality

    L*N <= (r+L-1) * #{x : (Fin m × Fin b) → G | ∃a, ∑i, x(i,a(i))=0}.

Here the right-hand count is an actual subtype cardinality, not an assumed
oracle answer count. Surjectivity gives exact single and distinct-pair
event counts, which give the first and second moments. Cauchy--Schwarz on
the actual support yields the displayed bound. Dividing by N interprets it
as uniform coverage at least L/(r+L-1); measure-theoretic notation is not
part of the formal statement. No relation-search algorithm is constructed.
Curve-cleanliness/label-conditioning and program/asymptotic costs remain
separate consumer obligations.

Initial prospective A1 at crypto983490ac55: prove coverage over existing finite
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
- 2e4b08b/build006 and canonical proofgate001 pass the full endpoint. No
  statement was weakened, proof limit raised, or native computation trusted.
