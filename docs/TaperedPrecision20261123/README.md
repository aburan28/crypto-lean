# Integer tapered-precision bounds

The Std-only `CryptoLeanCore.TaperedPrecision` module gives a finite scalar
bound for the precision expression in the Appendix D.11 contraction argument.
The source formula, a one-step increment bound and the conditional sharp bound
compile on the pinned Lean4.35.0 kernel. The accompanying local axiom query
lists only `propext` and `Quot.sound` for the two inequalities; the defining
formula has no axioms. These are producer checks, with no signed PCC standing.
[pcc:unverified]

`childPrecision p M u a i` assembles the source arithmetic
`p + 8*ceil(3M/u)*2^(a-i) + 8M(a+1)` using ordinary Nat operations.
For positive `u<=M`, `increment_le` bounds the zero-input increment by
`40*M*2^a`. The main scalar theorem uses `a=A+2u`, `i<u`, a root comparison
`s<=M*q`, inherited bound `p<=c*s*2^A`, and two independent dimension bounds:
`c*q*u<=2^(u+1)` and `8u(A+2u+1)<=2^(A+u+1)`. Its conclusion is
`u*childPrecision<=34*M*2^(a-i)`, without dividing integers.
[pcc:unverified]

The inherited coefficient `c` is a parameter, not a conclusion supplied by the
module. Its actual value for a recursive call history, the source's eventual
asymptotic absorption, graph/packet invariants, allocation and bit-work
accounting remain separate obligations. The scalar formula agrees with the
native shifted-packet formula on active inputs; bounded Rust overflow/error
behavior is not modeled. No graph admission, full counter proof or ECDLP
cost improvement follows from this module. [pcc:unverified]

Source: openai/math
`42907c9e999cc00d6abe7a50bfc1023250edd1b9`,
`preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/quantitative-contraction.tex`,
blob `51ba54efc29f51bbc0426f848003030da484f354`,
equation `tensor-precision-bound`; source SHA256
`671642d7b53154d92344e8c4be0240f18929632ebcfdf73b07c3e9939b873860`.
Native consumer: isogeny-labs/crypto PR4996, matching
`crates/hashed-ecdl-tensor/src/contraction/recursive.rs` on main816f9c3a.

This adds a shared resource model before study instances, as required by the
Lean instance gate. Existing Nat arithmetic supplies every order and algebra
law; no custom field, group, axiom, `sorry`, `native_decide` or changed
dependency/toolchain is introduced. Mathlib is not imported by this module.

The focused compiler/axiom checks do not discharge the complete library's
Mathlib build and CI gate. The PR remains draft while integration and the
source-bound scalar-history consumer continue. The native study carries one
positive scalar instance and six premise-deletion counterexamples; these are
not public admitted contraction graphs or additional solver executions.
[pcc:unverified]
