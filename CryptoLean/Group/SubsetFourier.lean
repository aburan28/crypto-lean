import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Combinatorics.Additive.Convolution
import Mathlib.Tactic

/-! Fourier bookkeeping for actual finite-group subsets. Consumer scope and
six-field inheritance plan: crypto38ae306f73; pre-edit floor probe:4cab4d5c88.
The existing character orthogonality law is used as stated. No analytic
elliptic character estimate or sampling model is asserted by these laws. -/
set_option autoImplicit false
namespace CryptoLean.SubsetFourier
open scoped BigOperators ComplexConjugate
variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def charSum (S : Finset G) (ψ : AddChar G ℂ) : ℂ := ∑ x ∈ S, ψ x

noncomputable def returnCount (S : Finset G) : ℕ := by
  classical
  exact ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, if x+y=z then 1 else 0

theorem charSum_trivial (S : Finset G) : charSum S 1 = (S.card : ℂ) := by
  simp [charSum]

/-- The finite-subset energy identity, by existing character orthogonality. -/
theorem energy (S : Finset G) :
    (∑ ψ : AddChar G ℂ, charSum S ψ * conj (charSum S ψ)) =
      (Fintype.card G : ℂ) * (S.card : ℂ) := by
  classical
  calc
    _ = ∑ ψ : AddChar G ℂ, ∑ x ∈ S, ∑ y ∈ S, ψ (x-y) := by
      apply Finset.sum_congr rfl
      intro ψ _
      simp only [charSum, map_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [ψ.map_sub_eq_div, div_eq_mul_inv, ψ.inv_apply_eq_conj]
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ ψ : AddChar G ℂ, ψ (x-y) := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ))) (t := S)]
    _ = _ := by
      simp [AddChar.sum_apply_eq_ite, sub_eq_zero, mul_comm]

theorem parseval (S : Finset G) :
    (∑ ψ : AddChar G ℂ, ‖charSum S ψ‖^2) =
      (Fintype.card G : ℝ) * (S.card : ℝ) := by
  have h := energy S
  simp_rw [Complex.mul_conj'] at h
  exact_mod_cast h

/-- Fourier representation of the actual ordered additive triples in S. -/
theorem triple_identity (S : Finset G) :
    (∑ ψ : AddChar G ℂ, charSum S ψ ^ 2 * conj (charSum S ψ)) =
      (Fintype.card G : ℂ) * (returnCount S : ℂ) := by
  classical
  calc
    _ = ∑ ψ : AddChar G ℂ, ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ψ (x+y-z) := by
      apply Finset.sum_congr rfl
      intro ψ _
      simp only [charSum, pow_two, map_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      rw [ψ.map_sub_eq_div, ψ.map_add_eq_mul, div_eq_mul_inv, ψ.inv_apply_eq_conj]
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ ψ : AddChar G ℂ, ψ (x+y-z) := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ))) (t := S)]
    _ = _ := by
      simp [AddChar.sum_apply_eq_ite, sub_eq_zero, returnCount, Finset.mul_sum, mul_ite]

end CryptoLean.SubsetFourier
