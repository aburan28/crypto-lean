import CryptoLean.PQ.KPKE
import CryptoLean.PQ.FO
import CryptoLean.Lattice.Negacyclic
import CryptoLean.Lattice.CBD
import CryptoLean.Lattice.Rounding

/-!
# ML-KEM (FIPS 203) as an instance of the generic proofs

The generic theorems of `KPKE.lean` and `FO.lean` are instantiated at ML-KEM's ring and
samplers, so the statements below are about ML-KEM itself, not about an abstract ring:

* `Rq = ℤ_3329[X]/(X^256 + 1)` (`NegacyclicRing 3329 256`), finite via its coefficient
  basis;
* `cbdPoly η`: FIPS 203 `SamplePolyCBD_η` from uniform coins, one uniform `w < 4^η`
  (that is, `2η` uniform bits) per coefficient, mapped by `cbdValue η`;
* `mlkem_indcpa`: for every `k` and every `(η₁, η₂)`, in particular ML-KEM-512
  (`k = 2, η₁ = 3, η₂ = 2`), ML-KEM-768 (`3, 2, 2`) and ML-KEM-1024 (`4, 2, 2`), the
  IND-CPA advantage against K-PKE is at most four decision-MLWE advantages of explicit
  reductions.

The per-coefficient correctness condition is `CryptoLean.Lattice.mlkem_decode_correct`
(decoding succeeds when the centred noise is below `832 = ⌈q/4⌋`), and the noise is the
term in `decrypt_encrypt`. Decapsulation correctness given K-PKE correctness is
`decaps_encaps`, and the failure-probability transfer in the ROM is `kemFail_le_pkeFail_rom`.
-/

set_option autoImplicit false

namespace CryptoLean.PQ.MLKEM

open CryptoLean.Lattice

/-- `R_q = ℤ_3329[X]/(X^256 + 1)`. -/
abbrev Rq := NegacyclicRing 3329 256

theorem n_ne_zero : (256 : ℕ) ≠ 0 := by norm_num

/-- Coefficient index type of `R_q` (it has 256 elements; `negacyclicPoly_natDegree`). -/
abbrev Idx := Fin (negacyclicPoly 3329 256).natDegree

noncomputable instance : Fintype Rq :=
  Fintype.ofEquiv _ (negacyclicBasis 3329 256 n_ne_zero).equivFun.toEquiv.symm

noncomputable instance : DecidableEq Rq := Classical.decEq _

/-- Coins for one `SamplePolyCBD_η` call: one uniform `w < 4^η` per coefficient. -/
abbrev CBDCoins (η : ℕ) := Idx → Fin (4 ^ η)

/-- FIPS 203 `SamplePolyCBD_η` as a function of uniform coins. -/
noncomputable def cbdPoly (η : ℕ) (w : CBDCoins η) : Rq :=
  (negacyclicBasis 3329 256 n_ne_zero).equivFun.symm
    fun i => ((cbdValue η (w i) : ℤ) : ZMod 3329)

/-- **IND-CPA of ML-KEM's K-PKE from decision Module-LWE**, for every parameter set. -/
theorem mlkem_indcpa (k η₁ η₂ : ℕ) {Ω : Type*} [Fintype Ω]
    (𝒜 : CPAAdversary Rq (Fin k) Ω) :
    |cpaGame (cbdPoly η₁) (cbdPoly η₂) 𝒜 true - cpaGame (cbdPoly η₁) (cbdPoly η₂) 𝒜 false|
      ≤ mlweAdv (cbdPoly η₁) (cbdPoly η₁) (B₁ (cbdPoly η₁) (cbdPoly η₂) 𝒜 true)
        + mlweAdv (cbdPoly η₁) (cbdPoly η₁) (B₁ (cbdPoly η₁) (cbdPoly η₂) 𝒜 false)
        + mlweAdv (cbdPoly η₁) (cbdPoly η₂) (B₂ 𝒜 true)
        + mlweAdv (cbdPoly η₁) (cbdPoly η₂) (B₂ 𝒜 false) :=
  indcpa_le_mlwe (cbdPoly η₁) (cbdPoly η₂) 𝒜

/-- ML-KEM-512 (`k = 2`, `η₁ = 3`, `η₂ = 2`). -/
theorem mlkem512_indcpa {Ω : Type*} [Fintype Ω] (𝒜 : CPAAdversary Rq (Fin 2) Ω) :
    |cpaGame (cbdPoly 3) (cbdPoly 2) 𝒜 true - cpaGame (cbdPoly 3) (cbdPoly 2) 𝒜 false|
      ≤ mlweAdv (cbdPoly 3) (cbdPoly 3) (B₁ (cbdPoly 3) (cbdPoly 2) 𝒜 true)
        + mlweAdv (cbdPoly 3) (cbdPoly 3) (B₁ (cbdPoly 3) (cbdPoly 2) 𝒜 false)
        + mlweAdv (cbdPoly 3) (cbdPoly 2) (B₂ 𝒜 true) + mlweAdv (cbdPoly 3) (cbdPoly 2) (B₂ 𝒜 false) :=
  mlkem_indcpa 2 3 2 𝒜

/-- ML-KEM-768 (`k = 3`, `η₁ = η₂ = 2`). -/
theorem mlkem768_indcpa {Ω : Type*} [Fintype Ω] (𝒜 : CPAAdversary Rq (Fin 3) Ω) :
    |cpaGame (cbdPoly 2) (cbdPoly 2) 𝒜 true - cpaGame (cbdPoly 2) (cbdPoly 2) 𝒜 false|
      ≤ mlweAdv (cbdPoly 2) (cbdPoly 2) (B₁ (cbdPoly 2) (cbdPoly 2) 𝒜 true)
        + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₁ (cbdPoly 2) (cbdPoly 2) 𝒜 false)
        + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₂ 𝒜 true) + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₂ 𝒜 false) :=
  mlkem_indcpa 3 2 2 𝒜

/-- ML-KEM-1024 (`k = 4`, `η₁ = η₂ = 2`). -/
theorem mlkem1024_indcpa {Ω : Type*} [Fintype Ω] (𝒜 : CPAAdversary Rq (Fin 4) Ω) :
    |cpaGame (cbdPoly 2) (cbdPoly 2) 𝒜 true - cpaGame (cbdPoly 2) (cbdPoly 2) 𝒜 false|
      ≤ mlweAdv (cbdPoly 2) (cbdPoly 2) (B₁ (cbdPoly 2) (cbdPoly 2) 𝒜 true)
        + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₁ (cbdPoly 2) (cbdPoly 2) 𝒜 false)
        + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₂ 𝒜 true) + mlweAdv (cbdPoly 2) (cbdPoly 2) (B₂ 𝒜 false) :=
  mlkem_indcpa 4 2 2 𝒜

end CryptoLean.PQ.MLKEM
