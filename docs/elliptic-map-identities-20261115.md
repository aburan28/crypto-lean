# Doubling and degree-two curve equations

Prospective scope, before the first build: four generic theorems support the
arbitrary-precision point-halving continuation in crypto. No native numerical
qualification has run for that port. The consumer protocol is
research/big_prime_halving_20261115/PROTOCOL.md at crypto bd458ef4e2.

The ring statements identify the cleared doubling quartic and the exact
Vélu curve residual. A kernel-root assumption gives the cleared codomain
equation; over a field, a source-point equation and nonzero denominator give
the affine codomain equation. There is no characteristic-specific finite
fixture, axiom, native_decide, new group-law definition or complexity claim.

Sources checked before implementation: MIT18.783 Fall2023 Lecture2 section2.2,
Lecture4 definitions4.18/4.20 and Lecture5 Theorem5.13; existing shared
ProjectiveVelu law; the consumer's prior native setup/complete-preimage code.
KB unavailable in the consumer runtime. The primary PDF hashes are retained
in the consumer protocol's checks/primary-sources.sha256.

Acceptance: the canonical shared build/source/axiom gate must pass, with only
propext, Classical.choice and Quot.sound and zero trusted native exceptions.
Retain any first-build diagnostic before source repair; no raised proof limit
or altered theorem statement merely to get a pass. Generic law correctness
does not formally bind the future native parser, arithmetic or isogeny program.

## Completed local gate

At source b38b6b4712017a6d87140f302c04d754a3280dce, all four statements
compiled on their first build. The canonical all-source gate then passed:
106 theorems audited, zero failures and zero trusted native exceptions.
The audit records only the standard foundations propext, Classical.choice
and Quot.sound. Lean is4.35.0 and mathlib is
cfc55fc58714a59dc06e6e79edc6d1d95140d3c2. No proof limit was raised.

The complete build/source/axiom logs and source SHA-256 manifest are retained
in [receipts/elliptic-map-identities-20261115](receipts/elliptic-map-identities-20261115).
This is a local proof receipt; hosted CI and PR review retain their own status.
The untracked ProjectiveVeluInstanceProbe.lean is unrelated and was not added
to the module inventory or this change.

The next consumer step is a GMP/FLINT implementation and separate OpenSSL
complete-root/group replay under its already frozen qualification protocol.
That numerical qualification has not run as of this proof receipt.
