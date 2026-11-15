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
