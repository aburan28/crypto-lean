import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# ECDLP across a prime conductor gap: floor/crater algebra

Laws behind the "large prime conductor gap" study
(`isogeny-labs/crypto research/deep_volcano_prime_gap_20261022/THEOREMS.md`),
stated over Mathlib structures, not over one curve:

* `QuadraticAlgebra ℤ a b` is an imaginary quadratic order `ℤ[ω]`,
  `ω² = a + bω`. `conductorOrder f` is its suborder `ℤ[fω]` (of index `|f|` when `f ≠ 0`; `ℤ` when `f = 0`).
* **Kohel, order form** (`smul_conductorOrder_le_iff`,
  `prime_dvd_degree_of_gap`): `d·O_f ⊆ O_g ↔ g ∣ d f`; so a prime `N` that
  divides one conductor and not the other divides every `d` with
  `d·O_f ⊆ O_g`.
* **Frobenius on `O/NO`** (`frobenius_scalar_iff`, `frobenius_eigen_card_le`,
  `scalar_trace_congr`): `π = x + yω` acts on `O/NO` as a scalar iff `N ∣ y`;
  otherwise every eigenspace of `π` on `O/NO ≅ (ZMod N)²` has at most `N`
  elements; a scalar is `t/2 mod N`.
* **Gap prime equal to the DLP prime** (`gap_prime_dvd_order`): in a class
  with `t² − 4p = D f²`, `N ∣ f` and `N ∣ #E = p + 1 − t`, we get
  `N ∣ p − 1` (embedding degree one), `N ∣ t − 2` and `N² ∣ #E`.
* **DLP transfer** (`dlog_transfer`, `addOrderOf_map_eq`): along an additive
  homomorphism `φ` with a "dual" `ψ`, `ψ ∘ φ = d •`, `gcd(d, n) = 1`, a
  logarithm in the image is the logarithm in the source.

Curve bridges *not* formalized here (Mathlib has no isogenies or
endomorphism rings of elliptic curves): `End(E) ≅ O_c`, `φ ∘ End(E) ∘ φ̂ =
d·End(E)` inside `K`, `E[N] ≅ O_c/N O_c` as `O_c`-modules (Lenstra 1996),
and `#E(F_p) = p + 1 − t`. They enter the endpoints as named hypotheses.
-/

set_option autoImplicit false

namespace CryptoLean.ConductorGap

open QuadraticAlgebra

variable {a b : ℤ}

/-! ## Orders of conductor `f` inside `ℤ[ω]` -/

/-- `ℤ[fω] = {x + yω : f ∣ y}`; for `f ≠ 0` the order of index `|f|` in `ℤ[ω]`, for `f = 0` just `ℤ`. -/
def conductorOrder (a b : ℤ) (f : ℤ) : Subring (QuadraticAlgebra ℤ a b) where
  carrier := {z | f ∣ z.im}
  mul_mem' := by
    rintro ⟨x, y⟩ ⟨u, v⟩ ⟨k, hk⟩ ⟨l, hl⟩
    simp only [Set.mem_ofPred_eq] at hk hl ⊢
    simp only [im_mul]
    refine ⟨x * l + k * u + b * k * v, ?_⟩
    rw [hk, hl]; ring
  one_mem' := by simp
  add_mem' := by
    rintro ⟨x, y⟩ ⟨u, v⟩ hy hv
    simpa using dvd_add hy hv
  zero_mem' := by simp
  neg_mem' := by
    rintro ⟨x, y⟩ hy
    simpa using hy

@[simp] theorem mem_conductorOrder {f : ℤ} {z : QuadraticAlgebra ℤ a b} :
    z ∈ conductorOrder a b f ↔ f ∣ z.im := Iff.rfl

/-- **Kohel's containment, order form.** `d · O_f ⊆ O_g` iff `g ∣ d f`. -/
theorem smul_conductorOrder_le_iff {f g d : ℤ} :
    (∀ z ∈ conductorOrder a b f, d • z ∈ conductorOrder a b g) ↔ g ∣ d * f := by
  constructor
  · intro h
    have := h ⟨0, f⟩ (by simp)
    simpa using this
  · rintro hg z ⟨k, hk⟩
    simp only [mem_conductorOrder, im_smul, smul_eq_mul, hk]
    exact (hg.mul_right k).trans ⟨1, by ring⟩

/-- **A prime in the gap divides the degree.** If an isogeny of degree `d`
gives `d · O_f ⊆ O_g` (curve bridge: `α ↦ φ α φ̂`), and the prime `N` divides
the conductor `g` but not `f`, then `N ∣ d`. -/
theorem prime_dvd_degree_of_gap {f g d N : ℤ} (hN : Prime N)
    (hcont : ∀ z ∈ conductorOrder a b f, d • z ∈ conductorOrder a b g)
    (hNg : N ∣ g) (hNf : ¬ N ∣ f) : N ∣ d := by
  have h := (smul_conductorOrder_le_iff.mp hcont)
  exact ((hN.dvd_or_dvd (hNg.trans h)).resolve_right hNf)

/-- Both directions of an isogeny across the gap: the prime divides the
degree whichever side is the floor. -/
theorem prime_dvd_degree_of_gap' {f g d N : ℤ} (hN : Prime N)
    (hdown : ∀ z ∈ conductorOrder a b f, d • z ∈ conductorOrder a b g)
    (hup : ∀ z ∈ conductorOrder a b g, d • z ∈ conductorOrder a b f)
    (hgap : (N ∣ g ∧ ¬ N ∣ f) ∨ (N ∣ f ∧ ¬ N ∣ g)) : N ∣ d := by
  rcases hgap with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact prime_dvd_degree_of_gap hN hdown h1 h2
  · exact prime_dvd_degree_of_gap hN hup h1 h2

/-! ## Frobenius acting on `O / N O` -/

/-- Reduction `ℤ[ω] → (ZMod N)[ω]`, i.e. `O → O/NO`. -/
abbrev reduce (a b : ℤ) (N : ℕ) :
    QuadraticAlgebra ℤ a b →+* QuadraticAlgebra (ZMod N) (a : ZMod N) (b : ZMod N) :=
  mapRingHom (Int.castRingHom (ZMod N)) a b

@[simp] theorem reduce_re (N : ℕ) (z : QuadraticAlgebra ℤ a b) :
    (reduce a b N z).re = (z.re : ZMod N) := rfl

@[simp] theorem reduce_im (N : ℕ) (z : QuadraticAlgebra ℤ a b) :
    (reduce a b N z).im = (z.im : ZMod N) := rfl

/-- **Scalar Frobenius.** `π` acts on `O/NO` as multiplication by `λ` iff
`N ∣ π.im` and `π.re ≡ λ (mod N)`. With `π = x + (f/c) ω_c` in `End(E) = O_c`,
`N ∣ π.im` says `N ∣ f/c`: the curve is on the side of the gap *above* `N`
(crater side, `N ∤ c`). -/
theorem frobenius_scalar_iff (N : ℕ) (π : QuadraticAlgebra ℤ a b) (lam : ZMod N) :
    (∀ z, reduce a b N π * z = lam • z) ↔ ((N : ℤ) ∣ π.im ∧ (π.re : ZMod N) = lam) := by
  constructor
  · intro h
    have h1 := h 1
    rw [mul_one] at h1
    have hre := congrArg QuadraticAlgebra.re h1
    have him := congrArg QuadraticAlgebra.im h1
    simp at hre him
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him, hre⟩
  · rintro ⟨hy, hx⟩ z
    have hred : reduce a b N π = algebraMap (ZMod N) _ lam := by
      ext
      · simpa using hx
      · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
    rw [hred, Algebra.smul_def]

/-- A scalar Frobenius on `O/NO` is `t/2`: `2λ ≡ tr π (mod N)`. -/
theorem scalar_trace_congr (N : ℕ) (π : QuadraticAlgebra ℤ a b) (lam : ZMod N)
    (h : ∀ z, reduce a b N π * z = lam • z) :
    ((trace π : ℤ) : ZMod N) = 2 * lam := by
  obtain ⟨hy, hx⟩ := (frobenius_scalar_iff N π lam).mp h
  have hy' : (π.im : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hy
  rw [trace_def]
  push_cast
  rw [hy', hx]; ring

/-- `O/NO` is a 2-dimensional `ZMod N`-space. -/
theorem finrank_reduce (N : ℕ) [Fact N.Prime] :
    Module.finrank (ZMod N) (QuadraticAlgebra (ZMod N) (a : ZMod N) (b : ZMod N)) = 2 :=
  QuadraticAlgebra.finrank_eq_two _ _

/-- **Non-scalar Frobenius has small eigenspaces.** If `N ∤ π.im` (the floor
side of the gap, `N ∣ c`), then for every `λ` the `λ`-eigenspace of `π` on
`O/NO` has at most `N` elements: a line, never `(ZMod N)²`. Via
`E[N] ≅ O_c/NO_c` this is "`E(F_p)[N]` (for `λ = 1`), resp. its twist, is
cyclic". -/
theorem frobenius_eigen_card_le (N : ℕ) [Fact N.Prime] (π : QuadraticAlgebra ℤ a b)
    (hy : ¬ (N : ℤ) ∣ π.im) (lam : ZMod N) :
    Nat.card {z : QuadraticAlgebra (ZMod N) (a : ZMod N) (b : ZMod N) //
      reduce a b N π * z = lam • z} ≤ N := by
  classical
  set V := QuadraticAlgebra (ZMod N) (a : ZMod N) (b : ZMod N)
  let T : V →ₗ[ZMod N] V := LinearMap.mulLeft (ZMod N) (reduce a b N π) - lam • LinearMap.id
  have hker : ∀ z : V, z ∈ LinearMap.ker T ↔ reduce a b N π * z = lam • z := by
    intro z; simp [T, sub_eq_zero]
  have hne : LinearMap.ker T ≠ ⊤ := by
    intro htop
    have : ∀ z : V, reduce a b N π * z = lam • z := fun z =>
      (hker z).mp (htop ▸ Submodule.mem_top)
    exact hy ((frobenius_scalar_iff N π lam).mp this).1
  have hlt : Module.finrank (ZMod N) (LinearMap.ker T) < 2 := by
    rw [← finrank_reduce (a := a) (b := b) N]
    exact Submodule.finrank_lt hne
  have hcard : Nat.card (LinearMap.ker T) =
      N ^ Module.finrank (ZMod N) (LinearMap.ker T) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod N), Nat.card_zmod]
  have hEq : Nat.card {z : V // reduce a b N π * z = lam • z} =
      Nat.card (LinearMap.ker T) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => (hker z).symm)
  rw [hEq, hcard]
  have hN : 1 ≤ N := (Fact.out : N.Prime).one_lt.le
  calc N ^ Module.finrank (ZMod N) (LinearMap.ker T) ≤ N ^ 1 :=
        Nat.pow_le_pow_right hN (by omega)
    _ = N := pow_one N

/-- The full `N`-eigenspace when Frobenius is scalar: all `N²` elements. -/
theorem frobenius_eigen_card_full (N : ℕ) [Fact N.Prime] (π : QuadraticAlgebra ℤ a b)
    (hy : (N : ℤ) ∣ π.im) :
    Nat.card {z : QuadraticAlgebra (ZMod N) (a : ZMod N) (b : ZMod N) //
      reduce a b N π * z = (π.re : ZMod N) • z} = N ^ 2 := by
  have hall := (frobenius_scalar_iff N π (π.re : ZMod N)).mpr ⟨hy, rfl⟩
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Module.natCard_eq_pow_finrank (K := ZMod N),
    Nat.card_zmod, finrank_reduce]

/-! ## The order `O_c` as its own quadratic algebra, and the two sides of the gap -/

/-- `ω_c = cω` satisfies `ω_c² = c²a + (cb) ω_c`: the generator of `O_c`. -/
theorem conductor_generator_sq (c : ℤ) :
    ((⟨0, c⟩ : QuadraticAlgebra ℤ a b)) * ⟨0, c⟩ =
      (c ^ 2 * a : ℤ) • (1 : QuadraticAlgebra ℤ a b) +
        (c * b : ℤ) • (⟨0, c⟩ : QuadraticAlgebra ℤ a b) := by
  ext <;> simp only [re_mul, im_mul, re_add, im_add, re_smul, im_smul, re_one, im_one,
    smul_eq_mul] <;> ring

/-- `O_c ≅ ℤ[ω_c]` with `ω_c² = c²a + (cb)ω_c`, mapped into `ℤ[ω]` by `ω_c ↦ cω`. -/
def orderEmbed (a b c : ℤ) :
    QuadraticAlgebra ℤ (c ^ 2 * a) (c * b) →ₐ[ℤ] QuadraticAlgebra ℤ a b :=
  lift ⟨⟨0, c⟩, conductor_generator_sq c⟩

theorem orderEmbed_apply (c : ℤ) (z : QuadraticAlgebra ℤ (c ^ 2 * a) (c * b)) :
    orderEmbed a b c z = ⟨z.re, c * z.im⟩ := by
  ext <;> simp [orderEmbed, mul_comm]

/-- The image of `orderEmbed c` is exactly `conductorOrder c`. -/
theorem range_orderEmbed (c : ℤ) :
    Set.range (orderEmbed a b c) = conductorOrder a b c := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    simp [orderEmbed_apply]
  · rintro ⟨k, hk⟩
    exact ⟨⟨w.re, k⟩, by rw [orderEmbed_apply]; ext <;> simp [hk]⟩

/-- Frobenius in `O_c`: `π = x + fω = x + e·ω_c` with `f = c e`. -/
theorem orderEmbed_frobenius (c e x : ℤ) :
    orderEmbed a b c ⟨x, e⟩ = ⟨x, c * e⟩ := by
  rw [orderEmbed_apply]

/-- **Crater side of the gap.** `End(E) = O_c` with `N ∤ c`, `N ∣ f = c e`:
Frobenius `x + e ω_c` is scalar on `O_c/NO_c`; its `x`-eigenspace is all `N²`
elements. -/
theorem crater_side_full (N : ℕ) [Fact N.Prime] {c e x : ℤ}
    (hNf : (N : ℤ) ∣ c * e) (hNc : ¬ (N : ℤ) ∣ c) :
    Nat.card {z : QuadraticAlgebra (ZMod N) ((c ^ 2 * a : ℤ) : ZMod N) ((c * b : ℤ) : ZMod N) //
      reduce (c ^ 2 * a) (c * b) N ⟨x, e⟩ * z = (x : ZMod N) • z} = N ^ 2 := by
  have hp : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  exact frobenius_eigen_card_full N ⟨x, e⟩ ((hp.dvd_or_dvd hNf).resolve_left hNc)

/-- **Floor side of the gap.** `End(E) = O_c` with `N ∣ c` and `N² ∤ f = c e`
(`N ∥ f`): every eigenspace of Frobenius on `O_c/NO_c` has at most `N`
elements. -/
theorem floor_side_line (N : ℕ) [Fact N.Prime] {c e x : ℤ}
    (hNc : (N : ℤ) ∣ c) (hexact : ¬ (N : ℤ) ^ 2 ∣ c * e) (lam : ZMod N) :
    Nat.card {z : QuadraticAlgebra (ZMod N) ((c ^ 2 * a : ℤ) : ZMod N) ((c * b : ℤ) : ZMod N) //
      reduce (c ^ 2 * a) (c * b) N ⟨x, e⟩ * z = lam • z} ≤ N := by
  apply frobenius_eigen_card_le N ⟨x, e⟩ _ lam
  intro he
  exact hexact (by rw [pow_two]; exact mul_dvd_mul hNc he)

/-! ## The gap prime as the DLP prime -/

/-- **Gap prime dividing the group order.** If `t² − 4p = D f²`, the odd prime
`N` divides the conductor index `f` and also `#E = p + 1 − t`, then
`N ∣ p − 1` (embedding degree one: MOV/Frey–Rück applies on every curve of
the class), `N ∣ t − 2`, and `N² ∣ #E`. -/
theorem gap_prime_dvd_order {p t D f N : ℤ} (hN : Prime N) (hodd : ¬ N ∣ 2)
    (hdisc : t ^ 2 - 4 * p = D * f ^ 2) (hNf : N ∣ f) (hNE : N ∣ p + 1 - t) :
    N ∣ p - 1 ∧ N ∣ t - 2 ∧ N ^ 2 ∣ p + 1 - t := by
  obtain ⟨g, rfl⟩ := hNf
  obtain ⟨e, he⟩ := hNE
  have ht : t = p + 1 - N * e := by linarith
  -- (p - 1)² = t² - 4p + (stuff)·N
  have hsq : N ∣ (p - 1) ^ 2 := by
    refine ⟨D * N * g ^ 2 + 2 * (p + 1) * e - N * e ^ 2, ?_⟩
    have : (p - 1) ^ 2 = t ^ 2 - 4 * p + 2 * (p + 1) * (N * e) - (N * e) ^ 2 := by
      rw [ht]; ring
    rw [this, hdisc]; ring
  have hp1 : N ∣ p - 1 := hN.dvd_of_dvd_pow hsq
  have ht2 : N ∣ t - 2 := by
    obtain ⟨u, hu⟩ := hp1
    exact ⟨u - e, by rw [ht]; linarith⟩
  refine ⟨hp1, ht2, ?_⟩
  -- 4 #E = (t - 2)² - D f²
  obtain ⟨v, hv⟩ := ht2
  have h4 : N ^ 2 ∣ 4 * (p + 1 - t) :=
    ⟨v ^ 2 - D * g ^ 2, by
      have : 4 * (p + 1 - t) = (t - 2) ^ 2 - (t ^ 2 - 4 * p) := by ring
      rw [this, hdisc, hv]; ring⟩
  have hcop : IsCoprime (N ^ 2) 4 := by
    have : IsCoprime N 2 := (Prime.coprime_iff_not_dvd hN).mpr hodd
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
    exact this.pow
  exact hcop.dvd_of_dvd_mul_left h4

/-! ## DLP transfer along a map with a coprime dual -/

section Transfer

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- **DLP transfer.** Let `φ : G → H`, `ψ : H → G` be additive with
`ψ (φ x) = d • x` (an isogeny and its dual), `P` of order `n` with
`gcd(d, n) = 1` and `Q ∈ ⟨P⟩`. Any logarithm of `φ Q` to base `φ P` is a
logarithm of `Q` to base `P`. The solver on `H` is arbitrary. -/
theorem dlog_transfer (φ : G →+ H) (ψ : H →+ G) (d : ℕ) (hdual : ∀ x, ψ (φ x) = d • x)
    {P Q : G} (hcop : Nat.Coprime d (addOrderOf P)) (hQ : Q ∈ AddSubgroup.zmultiples P)
    {k : ℤ} (hk : φ Q = k • φ P) : Q = k • P := by
  obtain ⟨m, rfl⟩ := hQ
  have h1 : (d : ℤ) • (m • P) = (d : ℤ) • (k • P) := by
    have := congrArg ψ hk
    simp only [map_zsmul, hdual] at this
    simpa [natCast_zsmul, smul_comm (d : ℕ)] using this
  have h2 : ((d : ℤ) * (m - k)) • P = 0 := by
    rw [mul_smul, sub_smul, smul_sub, h1, sub_self]
  have h3 : (addOrderOf P : ℤ) ∣ (d : ℤ) * (m - k) :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr h2
  have h4 : (addOrderOf P : ℤ) ∣ m - k :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast, Nat.Coprime]
      using hcop.symm)).dvd_of_dvd_mul_left h3
  have h5 : (m - k) • P = 0 := addOrderOf_dvd_iff_zsmul_eq_zero.mp h4
  simpa [sub_smul, sub_eq_zero] using h5

/-- The image of `P` keeps its order: `addOrderOf (φ P) = addOrderOf P`. -/
theorem addOrderOf_map_eq (φ : G →+ H) (ψ : H →+ G) (d : ℕ) (hdual : ∀ x, ψ (φ x) = d • x)
    {P : G} (hcop : Nat.Coprime d (addOrderOf P)) :
    addOrderOf (φ P) = addOrderOf P := by
  apply Nat.dvd_antisymm (addOrderOf_map_dvd φ P)
  have h : addOrderOf (d • P) = addOrderOf P := hcop.symm.addOrderOf_nsmul
  rw [← h, ← hdual]
  exact addOrderOf_map_dvd ψ (φ P)

end Transfer

end CryptoLean.ConductorGap
