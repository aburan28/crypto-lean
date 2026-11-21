import CryptoLean.Curve.ConductorGap
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Bridges for the conductor-gap theorems

Three of the four curve-to-algebra bridges that `ConductorGap` used as
named hypotheses are reduced here to textbook facts about elliptic curves
that are stated *as hypotheses on a preadditive category*, and the rest is
proved.

1. **Order classification** (`subring_eq_conductorOrder`): every subring of
   `ℤ[ω]` containing `ℤ[fω]` (`f ≠ 0` not needed) is `ℤ[cω]` for some `c ∣ f`.
   With `ℤ[π] = ℤ[fω] ⊆ End(E) ⊆ O_K` this gives `End(E) = O_c`, `c ∣ f`.
2. **Kohel's bridge** (`hom_conj_eq_smul`, `kohel_smul_le`,
   `gap_prime_dvd_isogeny_degree`): in any preadditive category, if
   `φ : X ⟶ Y`, `ψ : Y ⟶ X` satisfy `φ ≫ ψ = d • 𝟙`, `ψ ≫ φ = d • 𝟙`,
   `φ` intertwines `π` and `π'`, `ℤ[π]` has finite index in `End X`, and
   `ι, ι'` are additive embeddings into `ℤ[ω]` sending `𝟙 ↦ 1` and
   `π, π' ↦ π_K`, then `ι'(ψ ≫ α ≫ φ) = d · ι(α)`. Hence
   `d · End X ⊆ End Y` inside `ℤ[ω]`, and a prime dividing exactly one of the
   two conductors divides `d`.
3. **Rational `N`-torsion** (`sub_one_mem_smul_iff`, `floor_not_full`,
   `crater_full_iff`): `π − 1 ∈ N · O_c` iff `N ∣ (f/c)` and
   `N ∣ x − 1`. By Silverman III.4.11 this is `E[N] ⊆ E(F_p)`.

Category-level conventions: `f ≫ g` is "first `f`, then `g`".
-/

set_option autoImplicit false

namespace CryptoLean.ConductorGap

open QuadraticAlgebra CategoryTheory

variable {a b : ℤ}

/-! ## 1. Every order between `ℤ[fω]` and `ℤ[ω]` is `ℤ[cω]` -/

/-- The imaginary-part map `ℤ[ω] → ℤ`. -/
def imHom (a b : ℤ) : QuadraticAlgebra ℤ a b →+ ℤ where
  toFun z := z.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Order classification.** A subring `S` of `ℤ[ω]` with `ℤ[fω] ⊆ S` is
`ℤ[cω] = conductorOrder c` for some `c ∣ f`. -/
theorem subring_eq_conductorOrder (S : Subring (QuadraticAlgebra ℤ a b)) {f : ℤ}
    (hf : conductorOrder a b f ≤ S) : ∃ c : ℤ, c ∣ f ∧ S = conductorOrder a b c := by
  -- the ideal of imaginary parts of `S`
  let J : Ideal ℤ := AddSubgroup.toIntSubmodule (S.toAddSubgroup.map (imHom a b))
  obtain ⟨c, hc⟩ := (Submodule.IsPrincipal.principal J)
  have hJ : ∀ n : ℤ, n ∈ J ↔ c ∣ n := by
    intro n
    rw [hc, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
    · rintro ⟨k, rfl⟩; exact ⟨k, by rw [smul_eq_mul, mul_comm]⟩
  have hmemJ : ∀ n : ℤ, n ∈ J ↔ ∃ z ∈ S, z.im = n := by
    intro n
    show n ∈ (S.toAddSubgroup.map (imHom a b)) ↔ _
    simp [imHom]
  refine ⟨c, ?_, ?_⟩
  · exact (hJ f).mp ((hmemJ f).mpr ⟨⟨0, f⟩, hf (by simp), rfl⟩)
  · ext z
    constructor
    · intro hz
      exact (hJ z.im).mp ((hmemJ _).mpr ⟨z, hz, rfl⟩)
    · rintro ⟨k, hk⟩
      obtain ⟨s, hs, hsim⟩ := (hmemJ c).mpr ((hJ c).mpr dvd_rfl)
      have hsim' : s.im = c := hsim
      have hw : z - k • s = ((z - k • s).re : QuadraticAlgebra ℤ a b) := by
        ext
        · simp
        · simp [hk, hsim', mul_comm]
      have : z = ((z - k • s).re : QuadraticAlgebra ℤ a b) + k • s := by
        rw [← hw]; abel
      rw [this]
      exact S.add_mem (intCast_mem S _) (S.zsmul_mem hs k)

/-! ## 2. Kohel's bridge in a preadditive category -/

section Kohel

variable {C : Type*} [Category C] [Preadditive C] {X Y : C}

/-- Conjugating by an isogeny and its dual multiplies `ℤ[π]` by `d`:
`ψ ≫ (u • 𝟙 + v • π) ≫ φ = d • (u • 𝟙 + v • π')`. -/
theorem conj_polynomial (φ : X ⟶ Y) (ψ : Y ⟶ X) (d : ℤ)
    (hψφ : ψ ≫ φ = d • 𝟙 Y) (π : X ⟶ X) (π' : Y ⟶ Y) (hcomm : π ≫ φ = φ ≫ π')
    (u v : ℤ) :
    ψ ≫ (u • 𝟙 X + v • π) ≫ φ = d • (u • 𝟙 Y + v • π') := by
  simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, Category.id_comp, hcomm, ← Category.assoc, hψφ]
  simp only [smul_add, smul_smul, mul_comm]

/-- **Kohel's bridge.** Under normalized embeddings `ι, ι'` into `ℤ[ω]`
(additive, `𝟙 ↦ 1`, `π, π' ↦ πK`), and finite index of `ℤ[π]` in `End X`,
conjugation by an isogeny of degree `d` is multiplication by `d`:
`ι' (ψ ≫ α ≫ φ) = d • ι α`. -/
theorem hom_conj_eq_smul (φ : X ⟶ Y) (ψ : Y ⟶ X) (d : ℤ)
    (hψφ : ψ ≫ φ = d • 𝟙 Y) (π : X ⟶ X) (π' : Y ⟶ Y) (hcomm : π ≫ φ = φ ≫ π')
    (hindex : ∀ α : X ⟶ X, ∃ m : ℤ, m ≠ 0 ∧ ∃ u v : ℤ, m • α = u • 𝟙 X + v • π)
    (ι : (X ⟶ X) →+ QuadraticAlgebra ℤ a b) (ι' : (Y ⟶ Y) →+ QuadraticAlgebra ℤ a b)
    (πK : QuadraticAlgebra ℤ a b)
    (hι1 : ι (𝟙 X) = 1) (hιπ : ι π = πK) (hι'1 : ι' (𝟙 Y) = 1) (hι'π : ι' π' = πK)
    (α : X ⟶ X) : ι' (ψ ≫ α ≫ φ) = d • ι α := by
  obtain ⟨m, hm, u, v, huv⟩ := hindex α
  have h1 : m • ι' (ψ ≫ α ≫ φ) = m • (d • ι α) := by
    rw [← map_zsmul, ← Preadditive.comp_zsmul, ← Preadditive.zsmul_comp, huv,
      conj_polynomial φ ψ d hψφ π π' hcomm u v, smul_comm m d, ← map_zsmul ι, huv]
    simp [map_add, map_zsmul, hι1, hιπ, hι'1, hι'π]
  ext
  · have := congrArg QuadraticAlgebra.re h1
    simp only [re_smul, smul_eq_mul] at this
    simpa using mul_left_cancel₀ hm this
  · have := congrArg QuadraticAlgebra.im h1
    simp only [im_smul, smul_eq_mul] at this
    simpa using mul_left_cancel₀ hm this

/-- **`d · End X ⊆ End Y`.** If `ι` maps `End X` into `O_c` and `ι'` maps
`End Y` *onto* nothing more than `O_{c'}` (every element of `O_c` is some
`ι α`, every `ι' β ∈ O_{c'}`), then `d · O_c ⊆ O_{c'}`. -/
theorem kohel_smul_le (φ : X ⟶ Y) (ψ : Y ⟶ X) (d : ℤ)
    (hψφ : ψ ≫ φ = d • 𝟙 Y) (π : X ⟶ X) (π' : Y ⟶ Y) (hcomm : π ≫ φ = φ ≫ π')
    (hindex : ∀ α : X ⟶ X, ∃ m : ℤ, m ≠ 0 ∧ ∃ u v : ℤ, m • α = u • 𝟙 X + v • π)
    (ι : (X ⟶ X) →+ QuadraticAlgebra ℤ a b) (ι' : (Y ⟶ Y) →+ QuadraticAlgebra ℤ a b)
    (πK : QuadraticAlgebra ℤ a b)
    (hι1 : ι (𝟙 X) = 1) (hιπ : ι π = πK) (hι'1 : ι' (𝟙 Y) = 1) (hι'π : ι' π' = πK)
    {c c' : ℤ} (hsurj : ∀ z ∈ conductorOrder a b c, ∃ α, ι α = z)
    (hinto' : ∀ β, ι' β ∈ conductorOrder a b c') :
    ∀ z ∈ conductorOrder a b c, d • z ∈ conductorOrder a b c' := by
  intro z hz
  obtain ⟨α, rfl⟩ := hsurj z hz
  rw [← hom_conj_eq_smul φ ψ d hψφ π π' hcomm hindex ι ι' πK hι1 hιπ hι'1 hι'π α]
  exact hinto' _

/-- **Every isogeny across a prime conductor gap has degree divisible by the
gap prime.** `End X ≅ O_c`, `End Y ≅ O_{c'}` (normalized), `N` prime with
`N ∣ c'` and `N ∤ c`, then `N ∣ deg φ`. -/
theorem gap_prime_dvd_isogeny_degree (φ : X ⟶ Y) (ψ : Y ⟶ X) (d : ℤ)
    (hψφ : ψ ≫ φ = d • 𝟙 Y) (π : X ⟶ X) (π' : Y ⟶ Y) (hcomm : π ≫ φ = φ ≫ π')
    (hindex : ∀ α : X ⟶ X, ∃ m : ℤ, m ≠ 0 ∧ ∃ u v : ℤ, m • α = u • 𝟙 X + v • π)
    (ι : (X ⟶ X) →+ QuadraticAlgebra ℤ a b) (ι' : (Y ⟶ Y) →+ QuadraticAlgebra ℤ a b)
    (πK : QuadraticAlgebra ℤ a b)
    (hι1 : ι (𝟙 X) = 1) (hιπ : ι π = πK) (hι'1 : ι' (𝟙 Y) = 1) (hι'π : ι' π' = πK)
    {c c' N : ℤ} (hsurj : ∀ z ∈ conductorOrder a b c, ∃ α, ι α = z)
    (hinto' : ∀ β, ι' β ∈ conductorOrder a b c')
    (hN : Prime N) (hNc' : N ∣ c') (hNc : ¬ N ∣ c) : N ∣ d :=
  prime_dvd_degree_of_gap hN
    (kohel_smul_le φ ψ d hψφ π π' hcomm hindex ι ι' πK hι1 hιπ hι'1 hι'π hsurj hinto')
    hNc' hNc

end Kohel

/-! ## 3. Rational `N`-torsion: `π − 1 ∈ N · O_c` -/

/-- In `O_c = ℤ[ω_c]`, `π = x + eω_c`: `π − 1 ∈ N · O_c ↔ N ∣ e ∧ N ∣ x − 1`.
(Silverman III.4.11: `E[N] ⊆ ker(π − 1)` iff `π − 1 = [N] ∘ α` with `α`
an endomorphism; for ordinary `E`, `End(E) = End_{F_p}(E)`.) -/
theorem sub_one_mem_smul_iff {a' b' : ℤ} (N x e : ℤ) :
    (∃ α : QuadraticAlgebra ℤ a' b', (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 1 = N • α) ↔
      (N ∣ e ∧ N ∣ x - 1) := by
  constructor
  · rintro ⟨α, hα⟩
    have hre := congrArg QuadraticAlgebra.re hα
    have him := congrArg QuadraticAlgebra.im hα
    simp at hre him
    exact ⟨⟨α.im, him⟩, ⟨α.re, hre⟩⟩
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    exact ⟨⟨l, k⟩, by ext <;> simp [hk, hl]⟩

/-- **Floor side: never full rational `N`-torsion.** `N ∣ c`, `N² ∤ f = c e`
(`N ∥ f`) ⇒ `π − 1 ∉ N · O_c`, i.e. `E(F_p)[N]` is cyclic. -/
theorem floor_not_full {a' b' : ℤ} {N c e x : ℤ} (hNc : N ∣ c) (hexact : ¬ N ^ 2 ∣ c * e) :
    ¬ ∃ α : QuadraticAlgebra ℤ a' b', (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 1 = N • α := by
  rw [sub_one_mem_smul_iff]
  rintro ⟨he, -⟩
  exact hexact (by rw [pow_two]; exact mul_dvd_mul hNc he)

/-- **Crater side: full rational `N`-torsion iff `x ≡ 1 (mod N)`.** `N` prime,
`N ∤ c`, `N ∣ f = c e` ⇒ (`π − 1 ∈ N · O_c` ↔ `N ∣ x − 1`). Since then
`t ≡ 2x (mod N)`, for odd `N` this is `t ≡ 2 (mod N)`; the twist (Frobenius
`−π`) is full iff `t ≡ −2`. Otherwise neither is full over `F_p`. -/
theorem crater_full_iff {a' b' : ℤ} {N c e x : ℤ} (hN : Prime N) (hNf : N ∣ c * e)
    (hNc : ¬ N ∣ c) :
    (∃ α : QuadraticAlgebra ℤ a' b', (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 1 = N • α) ↔
      N ∣ x - 1 := by
  rw [sub_one_mem_smul_iff]
  exact ⟨And.right, fun h => ⟨(hN.dvd_or_dvd hNf).resolve_left hNc, h⟩⟩

/-- On the crater side the trace is `2x` mod `N`: `tr(x + eω_c) = 2x + b'e`. -/
theorem crater_trace_congr {a' b' : ℤ} {N e x : ℤ} (he : N ∣ e) :
    N ∣ trace (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 2 * x := by
  rw [trace_def]
  simpa using dvd_mul_of_dvd_right he b'

end CryptoLean.ConductorGap
