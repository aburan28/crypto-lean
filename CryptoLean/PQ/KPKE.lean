import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic
import CryptoLean.PQ.Games
import CryptoLean.Lattice.ModuleLWE

/-!
# K-PKE (Regev / LPR / Kyber / ML-KEM): correctness identity and IND-CPA from MLWE

The public-key encryption scheme inside ML-KEM (FIPS 203, Algorithms 13–15), stated over
any finite commutative ring `R` (ML-KEM: `R = ℤ_3329[X]/(X^256+1)`) and module rank
`ι` (ML-KEM: `Fin k`, `k ∈ {2,3,4}`), with noise produced from uniform coins by two
samplers `χ₁ : C₁ → R` (FIPS 203 `η₁`) and `χ₂ : C₂ → R` (`η₂`):

* `keyGen`:  `t = A s + e`, with `A` uniform and `s, e ← χ₁`;
* `encrypt`: `u = Aᵀ r + e₁`, `v = ⟪t, r⟫ + e₂ + μ`, with `r ← χ₁`, `e₁, e₂ ← χ₂`;
* `decrypt`: `v − ⟪u, s⟫`.

## What is proved

* `decrypt_encrypt`: decryption returns `μ` plus the noise `⟪e, r⟫ − ⟪e₁, s⟫ + e₂`
  (the identity `decrypt_identity` of `Lattice/ModuleLWE.lean`, specialised). With
  `mlkem_decode_correct` (`Lattice/Rounding.lean`) this is the full deterministic
  correctness condition.
* `indcpa_le_mlwe` (**the security reduction**): for every adversary `𝒜`, including one
  that picks its two messages after seeing the public key,

      |Pr[𝒜 ⇒ 1 | enc μ₁] − Pr[𝒜 ⇒ 1 | enc μ₀]|
        ≤ Σ_b Adv^{MLWE(k×k, χ₁, χ₁)}(B₁ 𝒜 b) + Σ_b Adv^{MLWE((k+1)×k, χ₁, χ₂)}(B₂ 𝒜 b),

  where `B₁`, `B₂` are explicit Lean terms (each runs `𝒜` once plus one encryption).
  This is the proof of Kyber's CPA security (Bos et al., EuroS&P 2018, Thm 1; LPR 2010)
  as three game hops: (0) the real game is MLWE-real for `B₁`; (1) with `t` uniform it
  is MLWE-real for `B₂` with the `(k+1)×k` matrix `[Aᵀ; tᵀ]` and secret `r`;
  (2) with `(u, v)` uniform the message is masked by a uniform `v`, so the game no
  longer depends on `b`.

## Modelling choices (read before citing)

* `A` is uniform. ML-KEM expands `A` from a 32-byte seed with SHAKE-128; treating that as
  uniform is the random-oracle step every published proof makes. Not proved here.
* The ciphertext is uncompressed. `Compress_du`, `Compress_dv` and `ByteEncode` are public
  deterministic maps of `(u, v)`, so an adversary against the compressed ciphertext is an
  adversary here composed with them; the bound is unchanged.
* The NTT is a public ring isomorphism and does not change any distribution.
* Advantages are exact rationals of finite uniform experiments; *running time* is not
  modelled. The reductions' efficiency is visible from their definitions but is not a
  Lean theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CryptoLean.PQ

open Matrix

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section MLWE

variable {κ Cs Ce Ω : Type*} [Fintype κ] [DecidableEq κ] [Fintype Cs] [Fintype Ce]
  [Fintype Ω]

/-- **Decision MLWE, real side.** `D` (with its own coins `ω`) sees `(A, A s + e)` for
uniform `A : R^{κ×ι}`, `s ← χs`, `e ← χe`. -/
def mlweReal (χs : Cs → R) (χe : Ce → R) (D : Ω → Matrix κ ι R → (κ → R) → Bool) : ℚ :=
  pr fun x : Matrix κ ι R × (ι → Cs) × (κ → Ce) × Ω =>
    D x.2.2.2 x.1 (x.1 *ᵥ (χs ∘ x.2.1) + χe ∘ x.2.2.1)

/-- **Decision MLWE, random side.** `D` sees `(A, b)` with both uniform. -/
def mlweRand (D : Ω → Matrix κ ι R → (κ → R) → Bool) : ℚ :=
  pr fun x : Matrix κ ι R × (κ → R) × Ω => D x.2.2 x.1 x.2.1

/-- Distinguishing advantage against decision MLWE. -/
def mlweAdv (χs : Cs → R) (χe : Ce → R) (D : Ω → Matrix κ ι R → (κ → R) → Bool) : ℚ :=
  |mlweReal χs χe D - mlweRand D|

end MLWE

section Scheme

variable {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂] (χ₁ : C₁ → R) (χ₂ : C₂ → R)

/-- K-PKE.KeyGen (FIPS 203 Alg. 13), from coins: public `t = A s + e`. -/
def keyGen (A : Matrix ι ι R) (sc ec : ι → C₁) : ι → R :=
  A *ᵥ (χ₁ ∘ sc) + χ₁ ∘ ec

/-- K-PKE.Encrypt (FIPS 203 Alg. 14), before compression, for an encoded message `μ`. -/
def encrypt (A : Matrix ι ι R) (t : ι → R) (μ : R) (rc : ι → C₁) (e₁c : ι → C₂)
    (e₂c : C₂) : (ι → R) × R :=
  (Aᵀ *ᵥ (χ₁ ∘ rc) + χ₂ ∘ e₁c, t ⬝ᵥ (χ₁ ∘ rc) + χ₂ e₂c + μ)

/-- K-PKE.Decrypt (FIPS 203 Alg. 15), before decoding: `v − ⟪u, s⟫`. -/
def decrypt (s : ι → R) (c : (ι → R) × R) : R :=
  c.2 - c.1 ⬝ᵥ s

/-- **Correctness identity.** Decrypting an honest ciphertext gives the message plus the
noise `⟪e, r⟫ − ⟪e₁, s⟫ + e₂`. -/
theorem decrypt_encrypt (A : Matrix ι ι R) (sc ec rc : ι → C₁) (e₁c : ι → C₂) (e₂c : C₂)
    (μ : R) :
    decrypt (χ₁ ∘ sc) (encrypt χ₁ χ₂ A (keyGen χ₁ A sc ec) μ rc e₁c e₂c)
      = μ + ((χ₁ ∘ ec) ⬝ᵥ (χ₁ ∘ rc) - (χ₂ ∘ e₁c) ⬝ᵥ (χ₁ ∘ sc) + χ₂ e₂c) := by
  unfold decrypt encrypt keyGen
  exact CryptoLean.Lattice.decrypt_identity A _ _ _ _ _ _

/-- An IND-CPA adversary with coins `Ω`. It chooses the message pair *after* seeing the
public key (`msg b ω A t` is the encoded `μ_b`) and then guesses from the ciphertext. -/
structure CPAAdversary (R ι Ω : Type*) where
  msg : Bool → Ω → Matrix ι ι R → (ι → R) → R
  guess : Ω → Matrix ι ι R → (ι → R) → (ι → R) × R → Bool

variable {Ω : Type*} [Fintype Ω]

/-- The IND-CPA experiment with challenge bit `b`: `Pr[𝒜 ⇒ 1 | Enc(pk, μ_b)]`. Coins:
matrix, key-generation coins, then the adversary's coins and the encryption coins. -/
def cpaGame (𝒜 : CPAAdversary R ι Ω) (b : Bool) : ℚ :=
  pr fun x : Matrix ι ι R × (ι → C₁) × (ι → C₁) × (Ω × (ι → C₁) × (ι → C₂) × C₂) =>
    let A := x.1
    let t := keyGen χ₁ A x.2.1 x.2.2.1
    let ω := x.2.2.2.1
    𝒜.guess ω A t (encrypt χ₁ χ₂ A t (𝒜.msg b ω A t) x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)

/-- **Reduction 1** (key indistinguishability): given an MLWE instance `(A, t)`, run the
IND-CPA game with public key `(A, t)` and fresh encryption coins. -/
def B₁ (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    Ω × (ι → C₁) × (ι → C₂) × C₂ → Matrix ι ι R → (ι → R) → Bool :=
  fun y A t => 𝒜.guess y.1 A t (encrypt χ₁ χ₂ A t (𝒜.msg b y.1 A t) y.2.1 y.2.2.1 y.2.2.2)

/-- The `(k+1)×k` matrix `[Aᵀ; tᵀ]`: row `some j` is column `j` of `A`, row `none` is `t`. -/
def stack (A : Matrix ι ι R) (t : ι → R) : Matrix (Option ι) ι R :=
  fun o => o.elim t (fun j i => A i j)

/-- Inverse of `stack`: read `A` and `t` back. -/
def unstackA (M : Matrix (Option ι) ι R) : Matrix ι ι R := fun i j => M (some j) i

/-- **Reduction 2** (ciphertext indistinguishability): given an MLWE instance `(M, y)`
with `M = [Aᵀ; tᵀ]`, use `(A, t)` as the public key and `(y_top, y_none + μ_b)` as the
ciphertext. -/
def B₂ (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    Ω → Matrix (Option ι) ι R → (Option ι → R) → Bool :=
  fun ω M y =>
    𝒜.guess ω (unstackA M) (M none)
      (fun j => y (some j), y none + 𝒜.msg b ω (unstackA M) (M none))

/-- Hop 0: the real IND-CPA game *is* MLWE-real for `B₁` (same coins, same values). -/
theorem cpaGame_eq_mlweReal (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    cpaGame χ₁ χ₂ 𝒜 b = mlweReal χ₁ χ₁ (B₁ χ₁ χ₂ 𝒜 b) := rfl

/-- The coin bijection behind hop 1: `(A, t, ω, r, e₁, e₂) ↦ ([Aᵀ; tᵀ], r, (e₂, e₁), ω)`. -/
def hop1Equiv :
    Matrix ι ι R × (ι → R) × (Ω × (ι → C₁) × (ι → C₂) × C₂) ≃
      Matrix (Option ι) ι R × (ι → C₁) × (Option ι → C₂) × Ω where
  toFun x := (stack x.1 x.2.1, x.2.2.2.1, fun o => o.elim x.2.2.2.2.2 x.2.2.2.2.1, x.2.2.1)
  invFun z := (unstackA z.1, z.1 none, z.2.2.2, z.2.1, fun j => z.2.2.1 (some j), z.2.2.1 none)
  left_inv x := by
    obtain ⟨A, t, ω, r, e₁, e₂⟩ := x
    rfl
  right_inv z := by
    obtain ⟨M, r, e, ω⟩ := z
    simp only [Prod.mk.injEq, and_true, true_and]
    constructor
    · funext o i
      cases o <;> rfl
    · funext o
      cases o <;> rfl

/-- Hop 1: with `t` uniform, the game is MLWE-real for `B₂` (secret `r`, errors
`(e₁, e₂)`, public matrix `[Aᵀ; tᵀ]`, which is uniform because `(A, t)` is). -/
theorem mlweRand_B₁_eq_mlweReal_B₂ (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    mlweRand (B₁ χ₁ χ₂ 𝒜 b) = mlweReal χ₁ χ₂ (B₂ 𝒜 b) := by
  unfold mlweRand mlweReal
  refine pr_eq_of_equiv (hop1Equiv (R := R) (ι := ι) (Ω := Ω) (C₁ := C₁) (C₂ := C₂)) _ _ ?_
  rintro ⟨A, t, ω, r, e₁, e₂⟩
  have hA : unstackA (stack A t) = A := rfl
  simp only [hop1Equiv, Equiv.coe_fn_mk, B₂, B₁, encrypt, hA]
  congr 2

/-- The final hybrid: everything the adversary sees is uniform and the message is not
used. -/
def B₂free (𝒜 : CPAAdversary R ι Ω) : Ω → Matrix (Option ι) ι R → (Option ι → R) → Bool :=
  fun ω M y => 𝒜.guess ω (unstackA M) (M none) (fun j => y (some j), y none)

/-- The coin bijection behind hop 2: shift the uniform `v` by the message (one-time pad). -/
def hop2Equiv (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    Matrix (Option ι) ι R × (Option ι → R) × Ω ≃ Matrix (Option ι) ι R × (Option ι → R) × Ω where
  toFun x := (x.1, Function.update x.2.1 none
    (x.2.1 none + 𝒜.msg b x.2.2 (unstackA x.1) (x.1 none)), x.2.2)
  invFun x := (x.1, Function.update x.2.1 none
    (x.2.1 none - 𝒜.msg b x.2.2 (unstackA x.1) (x.1 none)), x.2.2)
  left_inv x := by
    obtain ⟨M, y, ω⟩ := x
    simp only [Prod.mk.injEq, and_true, true_and, Function.update_self, add_sub_cancel_right]
    funext o
    cases o <;> simp [Function.update]
  right_inv x := by
    obtain ⟨M, y, ω⟩ := x
    simp only [Prod.mk.injEq, and_true, true_and, Function.update_self, sub_add_cancel]
    funext o
    cases o <;> simp [Function.update]

/-- Hop 2: with `(u, v)` uniform, `v + μ_b` is uniform, so the game does not depend on
`b`. -/
theorem mlweRand_B₂_eq_free (𝒜 : CPAAdversary R ι Ω) (b : Bool) :
    mlweRand (B₂ 𝒜 b) = mlweRand (B₂free 𝒜) := by
  unfold mlweRand
  refine pr_eq_of_equiv (hop2Equiv 𝒜 b) _ _ ?_
  rintro ⟨M, y, ω⟩
  simp [hop2Equiv, B₂, B₂free, Function.update]

/-- **IND-CPA security of K-PKE from decision MLWE.** For every IND-CPA adversary `𝒜`
the distinguishing advantage is at most the sum of four MLWE advantages of the explicit
reductions `B₁ 𝒜 b` (rank `k×k`, secret and error `χ₁`) and `B₂ 𝒜 b` (rank `(k+1)×k`,
secret `χ₁`, error `χ₂`). -/
theorem indcpa_le_mlwe (𝒜 : CPAAdversary R ι Ω) :
    |cpaGame χ₁ χ₂ 𝒜 true - cpaGame χ₁ χ₂ 𝒜 false|
      ≤ mlweAdv χ₁ χ₁ (B₁ χ₁ χ₂ 𝒜 true) + mlweAdv χ₁ χ₁ (B₁ χ₁ χ₂ 𝒜 false)
        + mlweAdv χ₁ χ₂ (B₂ 𝒜 true) + mlweAdv χ₁ χ₂ (B₂ 𝒜 false) := by
  unfold mlweAdv
  rw [cpaGame_eq_mlweReal, cpaGame_eq_mlweReal,
    ← mlweRand_B₁_eq_mlweReal_B₂, ← mlweRand_B₁_eq_mlweReal_B₂,
    mlweRand_B₂_eq_free, mlweRand_B₂_eq_free]
  set a₁ := mlweReal χ₁ χ₁ (B₁ χ₁ χ₂ 𝒜 true)
  set a₀ := mlweReal χ₁ χ₁ (B₁ χ₁ χ₂ 𝒜 false)
  set h₁ := mlweRand (B₁ χ₁ χ₂ 𝒜 true)
  set h₀ := mlweRand (B₁ χ₁ χ₂ 𝒜 false)
  set c := mlweRand (B₂free (Ω := Ω) (R := R) (ι := ι) 𝒜)
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self (a₁ - h₁), neg_abs_le (a₁ - h₁), le_abs_self (a₀ - h₀),
      neg_abs_le (a₀ - h₀), le_abs_self (h₁ - c), neg_abs_le (h₁ - c),
      le_abs_self (h₀ - c), neg_abs_le (h₀ - c)]

end Scheme

end CryptoLean.PQ
