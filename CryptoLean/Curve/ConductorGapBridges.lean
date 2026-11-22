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
3. **Rational `N`-torsion, algebraic criterion** (`sub_one_mem_smul_iff`,
   `sub_one_mem_smul_conductorOrder_iff`; any volcano height:
   `floor_not_full_of_not_dvd`, `above_floor_full_iff`; height one:
   `floor_not_full`, `crater_full_iff`): `π − 1 ∈ N · O_c` iff `N ∣ (f/c)` and
   `N ∣ x − 1`. That this is `E[N] ⊆ E(F_p)` (Silverman III.4.11) is a curve
   fact, not formalized here.
4. **Levels, cryptographic primes, chains** (`level_difference_le_degree`,
   `dlp_prime_not_dvd_conductor`, `HasDual.comp`, `dlog_transfer_of_hasDual`).

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

/-- **`d · End X ⊆ End Y`.** If every element of `O_c` is `ι α` for some
`α ∈ End X` (`ι` maps onto `O_c`) and every `ι' β` lies in `O_{c'}`, then
`d · O_c ⊆ O_{c'}`. -/
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

/-! ## 4. Volcano depth, cryptographic subgroups and chains -/

/-- **Level difference divides the degree.** `d · O_c ⊆ O_{c'}`,
`N^k ∣ c'`, `N ∤ c` (prime `N`) ⇒ `N^k ∣ d`: an isogeny from level `0` to
level `k` of the `N`-volcano has degree divisible by `N^k`. -/
theorem prime_pow_dvd_degree_of_gap {c c' d N : ℤ} (k : ℕ) (hN : Prime N)
    (hcont : ∀ z ∈ conductorOrder a b c, d • z ∈ conductorOrder a b c')
    (hNk : N ^ k ∣ c') (hNc : ¬ N ∣ c) : N ^ k ∣ d := by
  have h := smul_conductorOrder_le_iff.mp hcont
  have hcop : IsCoprime (N ^ k) c :=
    ((Prime.coprime_iff_not_dvd hN).mpr hNc).pow_left
  exact hcop.dvd_of_dvd_mul_right (hNk.trans h)

/-- **A cryptographic DLP prime never divides the conductor gap.** If `n` is
prime, `n ∣ #E = p + 1 − t`, `n² ∤ #E` (e.g. `n > √#E`), `n` odd and
`t² − 4p = D f²`, then `n ∤ f`. So every prime dividing `f` (every volcano
prime, every gap prime) is coprime to `n`. -/
theorem dlp_prime_not_dvd_conductor {p t D f n : ℤ} (hn : Prime n) (hodd : ¬ n ∣ 2)
    (hdisc : t ^ 2 - 4 * p = D * f ^ 2) (hnE : n ∣ p + 1 - t) (hsq : ¬ n ^ 2 ∣ p + 1 - t) :
    ¬ n ∣ f := fun hnf => hsq (gap_prime_dvd_order hn hodd hdisc hnf hnE).2.2

section Chain

variable {G H I : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]

/-- Duals compose: `(ψ₁ ∘ ψ₂) ∘ (φ₂ ∘ φ₁) = [d₂ d₁]`. -/
theorem dual_comp (φ₁ : G →+ H) (ψ₁ : H →+ G) (φ₂ : H →+ I) (ψ₂ : I →+ H) (d₁ d₂ : ℕ)
    (h₁ : ∀ x, ψ₁ (φ₁ x) = d₁ • x) (h₂ : ∀ y, ψ₂ (φ₂ y) = d₂ • y) :
    ∀ x, (ψ₁.comp ψ₂) ((φ₂.comp φ₁) x) = (d₁ * d₂) • x := by
  intro x
  simp only [AddMonoidHom.comp_apply, h₂, map_nsmul, h₁]
  rw [smul_smul, mul_comm]

/-- **Transfer along a chain** of two maps with duals of degrees coprime to
`ord P`. Iterating gives any finite chain. -/
theorem dlog_transfer_comp (φ₁ : G →+ H) (ψ₁ : H →+ G) (φ₂ : H →+ I) (ψ₂ : I →+ H)
    (d₁ d₂ : ℕ) (h₁ : ∀ x, ψ₁ (φ₁ x) = d₁ • x) (h₂ : ∀ y, ψ₂ (φ₂ y) = d₂ • y)
    {P Q : G} (hc₁ : Nat.Coprime d₁ (addOrderOf P)) (hc₂ : Nat.Coprime d₂ (addOrderOf P))
    (hQ : Q ∈ AddSubgroup.zmultiples P) {k : ℤ}
    (hk : φ₂ (φ₁ Q) = k • φ₂ (φ₁ P)) : Q = k • P :=
  dlog_transfer (φ₂.comp φ₁) (ψ₁.comp ψ₂) (d₁ * d₂) (dual_comp φ₁ ψ₁ φ₂ ψ₂ d₁ d₂ h₁ h₂)
    (Nat.coprime_mul_iff_left.mpr ⟨hc₁, hc₂⟩) hQ hk

end Chain

/-! ## 5. General levels: Kohel's bound between any two levels, floor and
non-floor criteria for any volcano height, and the criterion inside `ℤ[ω]` -/

/-- **Kohel's bound between arbitrary levels.** If `d · O_c ⊆ O_{c'}` with
`c, d ≠ 0`, then `v_N(c') ≤ v_N(d) + v_N(c)`. With the reverse inclusion
(the dual isogeny) this gives `|v_N(c) − v_N(c')| ≤ v_N(deg φ)`. -/
theorem level_le_degree_add (N : ℕ) [Fact N.Prime] {c c' d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hcont : ∀ z ∈ conductorOrder a b c, d • z ∈ conductorOrder a b c') :
    padicValInt N c' ≤ padicValInt N d + padicValInt N c := by
  have h := smul_conductorOrder_le_iff.mp hcont
  have hdc : d * c ≠ 0 := mul_ne_zero hd hc
  have := (padicValInt_dvd_iff (p := N) (padicValInt N c') (d * c)).mp
    ((padicValInt_dvd c').trans h)
  rw [← padicValInt.mul hd hc]
  exact this.resolve_left hdc

/-- Both directions: `|v_N(c) − v_N(c')| ≤ v_N(d)` for an isogeny of degree
`d` between curves with conductors `c, c'`. -/
theorem level_difference_le_degree (N : ℕ) [Fact N.Prime] {c c' d : ℤ}
    (hc : c ≠ 0) (hc' : c' ≠ 0) (hd : d ≠ 0)
    (hdown : ∀ z ∈ conductorOrder a b c, d • z ∈ conductorOrder a b c')
    (hup : ∀ z ∈ conductorOrder a b c', d • z ∈ conductorOrder a b c) :
    (padicValInt N c' : ℤ) - padicValInt N c ≤ padicValInt N d ∧
      (padicValInt N c : ℤ) - padicValInt N c' ≤ padicValInt N d := by
  have h1 := level_le_degree_add N hc hd hdown
  have h2 := level_le_degree_add N hc' hd hup
  omega

/-- **Floor, any height.** `N ∤ e` (`e = f/c`, i.e. `v_N(c) = v_N(f)`) ⇒
`π − 1 ∉ N · O_c`: no full rational `N`-torsion. -/
theorem floor_not_full_of_not_dvd {a' b' : ℤ} {N e x : ℤ} (he : ¬ N ∣ e) :
    ¬ ∃ α : QuadraticAlgebra ℤ a' b', (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 1 = N • α := by
  rw [sub_one_mem_smul_iff]
  exact fun h => he h.1

/-- **Above the floor, any height.** `N ∣ e` ⇒ (`π − 1 ∈ N · O_c` ↔ `N ∣ x − 1`). -/
theorem above_floor_full_iff {a' b' : ℤ} {N e x : ℤ} (he : N ∣ e) :
    (∃ α : QuadraticAlgebra ℤ a' b', (⟨x, e⟩ : QuadraticAlgebra ℤ a' b') - 1 = N • α) ↔
      N ∣ x - 1 := by
  rw [sub_one_mem_smul_iff]
  exact ⟨And.right, fun h => ⟨he, h⟩⟩

/-- **The criterion inside `ℤ[ω]`.** For `c ≠ 0` and `π = x + c e ω`
(`f = c e`): `π − 1 ∈ N · O_c` (with `O_c = conductorOrder c ⊆ ℤ[ω]`) iff
`N ∣ e` and `N ∣ x − 1`. This is `sub_one_mem_smul_iff` transported along
`orderEmbed`, stated with no auxiliary presentation. -/
theorem sub_one_mem_smul_conductorOrder_iff {c : ℤ} (hc : c ≠ 0) (N x e : ℤ) :
    (∃ α ∈ conductorOrder a b c, (⟨x, c * e⟩ : QuadraticAlgebra ℤ a b) - 1 = N • α) ↔
      (N ∣ e ∧ N ∣ x - 1) := by
  constructor
  · rintro ⟨α, ⟨v, hv⟩, hα⟩
    have hre := congrArg QuadraticAlgebra.re hα
    have him := congrArg QuadraticAlgebra.im hα
    simp only [re_sub, re_one, re_smul, smul_eq_mul, im_sub, im_one, sub_zero, im_smul] at hre him
    refine ⟨⟨v, ?_⟩, ⟨α.re, hre⟩⟩
    rw [hv] at him
    exact mul_left_cancel₀ hc (by rw [him]; ring)
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    refine ⟨⟨l, c * k⟩, by simp, ?_⟩
    ext
    · simp [hl]
    · simp [hk]; ring

/-! ## 6. Chains of any length -/

section HasDual

variable {G H I : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup I]

/-- `φ` has a dual of degree `d`: some `ψ` with `ψ ∘ φ = [d]`. -/
def HasDual (φ : G →+ H) (d : ℕ) : Prop := ∃ ψ : H →+ G, ∀ x, ψ (φ x) = d • x

/-- Composition of maps with duals has a dual of the product degree; by
induction this covers every finite chain `φ_r ∘ ⋯ ∘ φ_1`. -/
theorem HasDual.comp {φ₁ : G →+ H} {φ₂ : H →+ I} {d₁ d₂ : ℕ}
    (h₁ : HasDual φ₁ d₁) (h₂ : HasDual φ₂ d₂) : HasDual (φ₂.comp φ₁) (d₁ * d₂) := by
  obtain ⟨ψ₁, hψ₁⟩ := h₁
  obtain ⟨ψ₂, hψ₂⟩ := h₂
  exact ⟨ψ₁.comp ψ₂, dual_comp φ₁ ψ₁ φ₂ ψ₂ d₁ d₂ hψ₁ hψ₂⟩

/-- The identity has a dual of degree one (base of the chain induction). -/
theorem HasDual.id : HasDual (AddMonoidHom.id G) 1 := ⟨AddMonoidHom.id G, by simp⟩

/-- **Transfer along any map with a dual of degree prime to `ord P`**
(in particular along any finite chain built with `HasDual.comp`). -/
theorem dlog_transfer_of_hasDual {φ : G →+ H} {d : ℕ} (h : HasDual φ d) {P Q : G}
    (hcop : Nat.Coprime d (addOrderOf P)) (hQ : Q ∈ AddSubgroup.zmultiples P) {k : ℤ}
    (hk : φ Q = k • φ P) : Q = k • P := by
  obtain ⟨ψ, hψ⟩ := h
  exact dlog_transfer φ ψ d hψ hcop hQ hk

theorem addOrderOf_map_eq_of_hasDual {φ : G →+ H} {d : ℕ} (h : HasDual φ d) {P : G}
    (hcop : Nat.Coprime d (addOrderOf P)) : addOrderOf (φ P) = addOrderOf P := by
  obtain ⟨ψ, hψ⟩ := h
  exact addOrderOf_map_eq φ ψ d hψ hcop

end HasDual

end CryptoLean.ConductorGap
