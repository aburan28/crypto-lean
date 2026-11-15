# Retained powering and norm reconstruction

The consumer is crypto/research/norm_core_elimination_20261115. Its six-field
instance gate selects the Mathlib ring/polynomial structures and exact laws.
The target-root/monic-division and pre-wrap quotient/remainder assembly probe
type-checked before the missing generic law was written here.

The shared new law `retained_power_congruence` is over any commutative ring:
from V0=x and Vj^2=Qj*u+V(j+1), derive u | x^(2^n)-Vn. It composes the
existing difference-of-powers divisibility law by induction. No custom syntax,
ring operations or field algorithm is defined. `target_norm_division` applies
Mathlib's root/remainder theorem to the actual point and target-chart equations.
`retained_kummer_charts` combines actual retained transitions/terminal with the
existing norm-chart theorem; membership and charts are conclusions, not
assumptions. No composite object is unfolded beyond polynomial evaluation laws.

Unformalized consumer boundaries: full coefficient graph isomorphism and its
bounded witness lifting, exact implementation, backend provenance, growing-family
solver complexity/yield and the general prime-field ECDLP theorem. These generic
supporting laws do not discharge them. No changed pin or raised proof limit.
