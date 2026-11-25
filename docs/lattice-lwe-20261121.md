# LWE, Ring-LWE and Module-LWE in Lean: proof map (2026-11-21)

Modules: `CryptoLean/Lattice/{ModuleLWE,Negacyclic,Rounding,NTT,CBD}.lean`, imported
by `CryptoLean.Lattice` and `CryptoLean`. Research context and sources:
`isogeny-labs/knowledge` `reports/lwe-2026-11-21/` (survey).
Trunk task: isogeny-labs/workspace#52.

**What this is.** The exact algebra and the per-parameter certificates that LWE-based
schemes rest on. **What this is not.** No hardness statement, no reduction between
problems in the complexity sense, and no distributional claim beyond the uniform-error
bijection. Nothing here says anything about the security of ML-KEM, ML-DSA or any
parameter set.

## Gate receipt

`tools/proof-gate.sh --out <dir> .` on Lean v4.35.0 with the pinned Mathlib
`cfc55fc`: **PASS, 293 theorems in the package, 0 failing, 0 trusted
`native_decide`**. All 46 audited declarations of `CryptoLean.Lattice.*` (counting the
equation lemmas Lean generates for definitions) depend on at most
`propext, Classical.choice, Quot.sound`. Finite checks use `decide +kernel`, which is
checked by the kernel and adds no axiom. Run it again with `tools/proof-gate.sh .`.

## Instance statement (lean-instance-gate)

1. **Structure above.** A commutative ring `R` (Mathlib `CommRing`), `Fintype ι`
   for the module rank, `Matrix`/`dotProduct`/`mulVec` (Mathlib
   `Mathlib.Data.Matrix.Mul`). For flattening: a `K`-algebra `S` with
   `Module.Basis β K S` and `Algebra.leftMulMatrix`. For roots: `CommMonoid`,
   `orderOf`, `IsPrimitiveRoot`, `ZMod p`. For rounding: a `FloorRing` field and
   `round`.
2. **Theorems used as stated.** `dotProduct_add`, `add_dotProduct`,
   `smul_dotProduct`, `dotProduct_transpose_mulVec`,
   `Algebra.leftMulMatrix_mulVec_repr`, `Fintype.sum_prod_type`,
   `orderOf_eq_prime_pow`, `IsPrimitiveRoot.orderOf`,
   `ZMod.orderOf_dvd_card_sub_one`, `abs_sub_round`,
   `ZMod.intCast_eq_intCast_iff`, `ZMod.coe_valMinAbs`,
   `AdjoinRoot.eval₂_root`, `AdjoinRoot.powerBasis'`.
3. **Objects as instances.** LWE is `sample` at `R = ZMod q`, `ι = Fin n`.
   Ring-LWE is `ι = Fin 1` (`sample_fin_one`). Module-LWE is
   `R = NegacyclicRing q n = AdjoinRoot (X^n + C 1)`, `ι = Fin d`. ML-KEM is
   `q = 3329, n = 256, d ∈ {2,3,4}` and ML-DSA is `q = 8380417, n = 256`.
4. **Assembly probe.** `mlwe_coeff_is_lwe` is `repr_sample` applied to the power
   basis, a one-line endpoint. `mlkem_decode_correct` composes the integer table with
   the `ZMod` bridge.
5. **Missing components built.** The definitions `sample`, `shift`, `flatMatrix`,
   `flatVec`, `negacyclicPoly`, the FIPS 203 `Compress`/`Decompress` in integer form,
   and `cbdValue`. The two generic laws `isPrimitiveRoot_two_pow` and
   `zmod_pow_eq_of_nat` are upstream candidates for Mathlib.
6. **Inheritance table.**

| statement | kind | owner | from |
|:--|:--|:--|:--|
| `residual_sample`, `residual_sample_of_ne` | law | ModuleLWE | `dotProduct_sub`, `ring` |
| `shift_sample` (self-reduction in the secret) | law | ModuleLWE | `dotProduct_add` |
| `sample_add`, `sample_smul`, `sample_neg`, `sample_sum` (sample combination, BKW and dual) | law | ModuleLWE | `add_dotProduct`, `smul_dotProduct`, induction on `Finset` |
| `sample_injective`, `sample_bijective`, `card_sample_preimage` (uniform error hides the secret) | law | ModuleLWE | the explicit inverse `(a, b) ↦ (a, b - ⟪a, s⟫)` |
| `samples_row` | law | ModuleLWE | `mulVec` unfolds to `dotProduct` by `rfl`/`simp` |
| `decrypt_identity` (Regev, LPR, Kyber-PKE) | law | ModuleLWE | `dotProduct_transpose_mulVec` |
| `sample_fin_one` (Ring-LWE as rank one) | instance | ModuleLWE | `Fin.sum_univ_one` |
| `repr_sample` (MLWE over a free algebra is LWE) | law | ModuleLWE | `Algebra.leftMulMatrix_mulVec_repr`, `Fintype.sum_prod_type` |
| `negacyclic_X_pow`, `negacyclicPoly_monic`, `negacyclicPoly_natDegree` | instance | Negacyclic | `AdjoinRoot.eval₂_root`, `monic_X_pow_add_C`, `natDegree_X_pow_add_C` |
| `mlwe_coeff_is_lwe` | endpoint | Negacyclic | `repr_sample` |
| `lwr_error` (LWR is LWE with error at most `q/2p`) | law | Rounding | `abs_sub_round` |
| `mlkem_decompress_compress_error` (FIPS 203 §4.2.1 bound, `d ∈ {1,4,5,10,11}`) | certificate | Rounding | checker `compressBoundHolds` and its soundness theorem, then `decide +kernel` |
| `mlkem_decode_table`, `mlkem_decode_int`, `mlkem_decode_correct` | certificate + endpoint | Rounding | `decide +kernel`, `omega`, the `ZMod` bridge |
| `isPrimitiveRoot_two_pow` | law | NTT | `orderOf_eq_prime_pow` |
| `mlkem_zeta`, `mldsa_zeta` | instance | NTT | `isPrimitiveRoot_two_pow` with `Nat` power residues computed by `norm_num` |
| `mlkem_no_512th_root` | instance | NTT | `ZMod.orderOf_dvd_card_sub_one` |
| `mlkem_q_prime`, `mldsa_q_prime` | instance | NTT | `norm_num` prime extension |
| `cbd_support`, `cbd_mean_zero`, `cbd_variance`, `cbd_counts_2`, `cbd_counts_3` | certificate | CBD | `decide +kernel` over all `4^η` bit strings |

## How the pieces compose: ML-KEM decryption, per coefficient

`decrypt_identity` gives `v - ⟪u, s⟫ = μ + n` with
`n = ⟪e, r⟫ - ⟪e₁, s⟫ + e₂` (plus compression errors, each bounded by
`mlkem_decompress_compress_error`). Then `mlkem_decode_correct` says that decoding
returns the message bit if every coefficient of `n` has centred size below 832. What
is **not** formalized is the probability that this bound holds, i.e. the
decryption-failure rate. FIPS 203 Table 1 reports it, and the Otto lab
(`isogeny-labs/otto` `examples/lwe`) recomputes it under the Kyber independence
heuristic with a certificate checker. A Lean proof of that tail bound would need a
formal convolution of distributions, and that is open work.

## Open, in order of value

1. Prove that `X^256 + 1 = ∏_{i<128} (X^2 - ζ^(2·brv₇(i)+1))` over `ZMod 3329`
   (the incomplete NTT), using a generic `X^(2n) + 1` factorisation law over a field
   with a primitive `4n`-th root. Today only the Otto certificate checks it.
2. A generic `ZMod p` law: a primitive `m`-th root of unity exists iff `m ∣ p - 1`
   (from `IsCyclic` of the units). It would replace the per-`q` certificates.
3. The distributional layer: `PMF`/`Measure` statements for decision-LWE
   advantage, with `sample_bijective` as the first lemma (uniform error gives
   advantage zero).
4. A general-`q` proof of `mlkem_decode_correct`. The current proof is per
   instance.
