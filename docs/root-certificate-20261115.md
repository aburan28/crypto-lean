# Root-completeness certificate

Prospective plan, recorded before the first build: two semantic theorems make
the consumer's normalized-gcd test precise. First, if g vanishes at every
field element and normalize(gcd(f,g)) is the product over a finite claimed
root set, that set is exactly the roots of f. Second, over a finite field use
g=X^|K|-X. Repeated roots of f are allowed; the claimed set has distinct roots.

Sources checked: MIT18.783 Fall2023 Lecture3 roots, and the pinned mathlib
FieldDivision.eval_gcd_eq_zero/isRoot_gcd_iff_isRoot_left_right,
roots_normalize/roots_prod_X_sub_C and FiniteField.pow_card. KB unavailable
in the consumer runtime. This uses existing results without a novelty claim.

The point-halving consumer source f5b318b482 has been frozen and pushed, but
no numerical qualification has run: its required S3 checkpoint gate failed
for unavailable upload access. This additional proof work is independent of
that gate and changes neither the frozen numerical protocol nor its caps.

Acceptance is the canonical all-source/axiom gate, only the standard three
foundations and zero trusted native exceptions. Preserve the first compile
diagnostic and theorem statements on repairs; no proof-limit increase. These
theorems do not verify the native parser, polynomial operations, primality,
integer/field encoding, curve doubling or an ECDLP solver.

## Completed local gate

Both semantic statements compile on their first build at source
7364d8dab7014a8bc610ed6911e7fb0839f6d47d. The canonical all-source gate
passes108theorems with0failures and0trusted native exceptions, using only
propext, Classical.choice and Quot.sound. No limit was raised. Complete first-
build, all-source and axiom logs plus source hashes are retained under
receipts/root-certificate-20261115. Hosted CI retains its own status.
