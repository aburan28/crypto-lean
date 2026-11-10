-- CryptoLean/SplitPrime/GaloisData.lean
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.GCD.Basic
import CryptoLean.SplitPrime.Obstruction

set_option autoImplicit false

namespace CryptoLean.SplitPrime

/-- (iii)(a), group form: if `gcd(ℓ, #G) = 1` the only `ℓ`-torsion element of `G` is `0`.
Applied to `G = E(F_p)` of prime order `n` and `ℓ ≠ n`: `E[ℓ] ∩ E(F_p) = {O}`. -/
theorem eq_zero_of_nsmul_eq_zero_of_coprime {G : Type*} [AddGroup G] [Finite G]
    {ℓ : ℕ} (hℓ : Nat.Coprime ℓ (Nat.card G)) {x : G} (hx : ℓ • x = 0) : x = 0 := by
  have h : addOrderOf x ∣ Nat.gcd ℓ (Nat.card G) :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hx) (addOrderOf_dvd_natCard x)
  rw [hℓ.gcd_eq_one] at h
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

/-- (iii)(b): a bi-additive pairing of an `ℓ`-torsion point with an `n`-torsion point,
`gcd(ℓ, n) = 1`, is trivial. For `e_ℓ`/Tate with values in `μ ⊆ Kˣ` take `M = Additive Kˣ`.
This is the whole content of "t^ℓ = t^n = 1 hence t = 1". -/
theorem pairing_eq_zero_of_coprime {A B M : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup M] (t : A →+ B →+ M) {ℓ n : ℕ} (h : Nat.Coprime ℓ n) {T : A} {P : B}
    (hT : ℓ • T = 0) (hP : n • P = 0) : t T P = 0 := by
  have h1 : ℓ • t T P = 0 := by
    rw [← AddMonoidHom.nsmul_apply, ← map_nsmul, hT, map_zero, AddMonoidHom.zero_apply]
  have h2 : n • t T P = 0 := by
    rw [← map_nsmul, hP, map_zero]
  have h3 : addOrderOf (t T P) ∣ Nat.gcd ℓ n :=
    Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero h1) (addOrderOf_dvd_of_nsmul_eq_zero h2)
  rw [h.gcd_eq_one] at h3
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

section Fiber
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The fiber of `φ` over `φ P` is the coset `P + ker φ`. -/
theorem mem_fiber_iff (φ : A →+ B) (P Q : A) : φ Q = φ P ↔ Q - P ∈ φ.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]

/-- (iii)(c): translation by `P` identifies `ker φ` with the fiber above `φ P`. -/
def fiberEquiv (φ : A →+ B) (P : A) : φ.ker ≃ {Q : A // φ Q = φ P} where
  toFun T := ⟨P + T.1, by rw [map_add, AddMonoidHom.mem_ker.mp T.2, add_zero]⟩
  invFun Q := ⟨Q.1 - P, (mem_fiber_iff φ P Q.1).mp Q.2⟩
  left_inv T := Subtype.ext (add_sub_cancel_left P T.1)   -- CHECK: post-2024 name
  right_inv Q := Subtype.ext (add_sub_cancel P Q.1)       -- CHECK: post-2024 name

/-- A `σ`-rational `φ` has `σ`-stable kernel. -/
theorem map_mem_ker (φ : A →+ B) (σA : A →+ A) (σB : B →+ B)
    (hcomm : ∀ x, φ (σA x) = σB (φ x)) {T : A} (hT : T ∈ φ.ker) : σA T ∈ φ.ker := by
  rw [AddMonoidHom.mem_ker] at hT ⊢
  rw [hcomm, hT, map_zero]

/-- (iii)(c), Galois part: for `σ`-fixed `P`, `σ` acts on the fiber `P + ker φ` through its
action on `ker φ`. Hence the Galois set `φ⁻¹(φ P)` is the same for every `P ∈ E(F_p)`. -/
theorem fiberEquiv_equivariant (φ : A →+ B) (σA : A →+ A) (P : A) (hP : σA P = P)
    (T : φ.ker) : σA (fiberEquiv φ P T).1 = P + σA T.1 := by
  show σA (P + T.1) = P + σA T.1
  rw [map_add, hP]
end Fiber

/-- Item (i) tightened: injectivity from a coprime kernel, the abstract form of
"`deg φ` prime to `n` ⇒ `ker φ ∩ E(F_p) = 0`". The missing link `#(ker φ) ∣ deg φ`
(separable isogenies) has no Mathlib counterpart. -/
theorem injective_of_coprime_ker_card {G H : Type*} [AddGroup G] [AddGroup H] [Finite G]
    (f : G →+ H) (h : Nat.Coprime (Nat.card f.ker) (Nat.card G)) : Function.Injective f := by
  have hd : Nat.card f.ker ∣ Nat.card G := AddSubgroup.card_addSubgroup_dvd_card f.ker
  have h1 : Nat.card f.ker = 1 := by
    have := Nat.dvd_gcd (dvd_refl _) hd
    rw [h.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  exact (AddMonoidHom.ker_eq_bot_iff f).1 (AddSubgroup.eq_bot_of_card_eq _ h1)

/-- Two isomorphisms between cyclic groups of prime order differ by a scalar. Needed by the
corollary: two rational isogenies `φ, ψ : E → E'` agree on `E(F_p)` up to a scalar `c`. -/
theorem exists_scalar_of_two_isos {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [IsAddCyclic H] (φ : G ≃+ H) (ψ : G →+ H) : ∃ c : ℤ, ∀ x, ψ x = c • φ x := by
  obtain ⟨c, hc⟩ := endo_cyclic_eq_zsmul (ψ.comp φ.symm.toAddMonoidHom)
  exact ⟨c, fun x => by simpa using hc (φ x)⟩

end CryptoLean.SplitPrime
