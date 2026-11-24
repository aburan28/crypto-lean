# Genuine additive pair-incidence retraction law

New generic law upstream of crypto5114; rootAGENTS and docs/DESIGN read.
Mathlib pin cfc55fc58714a59dc06e6e79edc6d1d95140d3c2 and its
Mathlib/Algebra/Group/Hom/Defs.lean were inspected. The file provides the
actual bundled AddMonoidHom types, function coercions, composition,
map_add/map_zero laws. Only that defining module is needed; no private
replacement Group/Hom structure or custom axiom is introduced.
[pcc:unverified]

Crypto actual dependency: degree4 S4 map and actual quotient correspondences
in research/chained_cm19_resolvents_20261124/ACTUAL_INCIDENCE_PRYM_PROOF_B.md,
claimd76527 and native7dafac. That written actual-object proof establishes
PsiAdj Psi=2I+Ldagger L, a split input kappa in ker L and rho*kappa=I.
The formal law proves only the additive consequence chi*Gamma=2 and
injectivity when doubling on the source is injective. It does not prove
quotient normalization, divisor correspondences, Jacobians, prime torsion
or their application to those actual objects. [pcc:unverified]

Use inherited AddMonoid structures and actual bundled homomorphisms on
arbitrary actual types; group inverses/commutativity are unnecessary.
First theorem unfolds the Gram identity at input a, kills norm(input a),
then applies the retract's map_add and left-inverse identity. Second theorem
applies the first to equal transfer images and uses injectivity of doubling.
All hypotheses appear explicitly; no circular assumption of transfer
injectivity and no finite/dummy-group proxy. [pcc:unverified]

Canonical tools/AuditAxioms.lean from current main is retained unchanged;
only standard foundations allowed and no trusted-native exemption. The
prior Mathlib Instances/product/ZMod profile's2GiB memory/import negatives
remain intact. This first attempt imports only homomorphism DEFINITIONS,
a materially smaller dependency surface, on the same scientific cap and
successful standard startup settings. If it fails, preserve the full first
failure and do not repeat it unchanged or increase logical/resource limits.
No claim of novelty; KB tools unavailable, no absence clearance.
[pcc:unverified]
