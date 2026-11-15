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

omit [Fintype G] in
theorem charSum_trivial (S : Finset G) : charSum S 1 = (S.card : ℂ) := by
  simp [charSum]

/-- The finite-subset energy identity, by existing character orthogonality. -/
theorem energy (S : Finset G) :
    (∑ ψ : AddChar G ℂ, charSum S ψ * conj (charSum S ψ)) =
      (Fintype.card G : ℂ) * (S.card : ℂ) := by
  classical
  calc
    _ = ∑ ψ : AddChar G ℂ, ∑ x ∈ S, ∑ y ∈ S, ψ (y-x) := by
      apply Finset.sum_congr rfl
      intro ψ _
      simp only [charSum, map_sum, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [ψ.map_sub_eq_div, div_eq_mul_inv, ψ.inv_apply_eq_conj]
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ ψ : AddChar G ℂ, ψ (y-x) := by
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
    _ = ∑ ψ : AddChar G ℂ, ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ψ (y+z-x) := by
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
      ring
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ z ∈ S, ∑ ψ : AddChar G ℂ, ψ (y+z-x) := by
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (AddChar G ℂ))) (t := S)]
    _ = ∑ y ∈ S, ∑ z ∈ S, ∑ x ∈ S, ∑ ψ : AddChar G ℂ, ψ (y+z-x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_comm
    _ = _ := by
      rw [returnCount]
      push_cast
      simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, Finset.mul_sum, mul_ite,
        mul_one, mul_zero]

/-- A flatness-conditioned norm endpoint on the actual finite subset.
The analytic bound M is an explicit hypothesis, not a curve axiom. -/
theorem triple_deviation_scaled (S : Finset G) (M : ℝ) (hM : 0 ≤ M)
    (hflat : ∀ ψ : AddChar G ℂ, ψ ≠ 1 → ‖charSum S ψ‖ ≤ M) :
    ‖(Fintype.card G : ℂ) * (returnCount S : ℂ) - (S.card : ℂ)^3‖ ≤
      M * (Fintype.card G : ℝ) * (S.card : ℝ) := by
  classical
  have ht : charSum S 1 ^ 2 * conj (charSum S 1) = (S.card : ℂ)^3 := by
    rw [charSum_trivial]
    simp
    ring
  have hsplit : (∑ ψ : AddChar G ℂ, charSum S ψ ^ 2 * conj (charSum S ψ)) -
      (S.card : ℂ)^3 =
      ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 1,
        charSum S ψ ^ 2 * conj (charSum S ψ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 1), ht, add_sub_cancel_right]
  rw [← triple_identity, hsplit]
  calc
    _ ≤ ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 1,
        ‖charSum S ψ ^ 2 * conj (charSum S ψ)‖ := norm_sum_le _ _
    _ = ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 1, ‖charSum S ψ‖^3 := by
      apply Finset.sum_congr rfl
      intro ψ _
      simp [norm_mul, norm_pow]
      ring
    _ ≤ ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 1, M*‖charSum S ψ‖^2 := by
      apply Finset.sum_le_sum
      intro ψ hψ
      have hf := hflat ψ (Finset.ne_of_mem_erase hψ)
      nlinarith [sq_nonneg ‖charSum S ψ‖]
    _ = M * ∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 1, ‖charSum S ψ‖^2 := by
      rw [Finset.mul_sum]
    _ ≤ M * ∑ ψ : AddChar G ℂ, ‖charSum S ψ‖^2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun _ _ _ => sq_nonneg _)
    _ = M * ((Fintype.card G : ℝ) * (S.card : ℝ)) := by rw [parseval]
    _ = _ := by ring

/-- Unscaled count deviation. No uniform-list or elliptic input is hidden. -/
theorem triple_deviation (S : Finset G) (M : ℝ) (hM : 0 ≤ M)
    (hflat : ∀ ψ : AddChar G ℂ, ψ ≠ 1 → ‖charSum S ψ‖ ≤ M) :
    |(returnCount S : ℝ) - (S.card : ℝ)^3 / (Fintype.card G : ℝ)| ≤
      M * (S.card : ℝ) := by
  have h := triple_deviation_scaled S M hM hflat
  have hc : (Fintype.card G : ℂ) * (returnCount S : ℂ) - (S.card : ℂ)^3 =
      (((Fintype.card G : ℝ) * (returnCount S : ℝ) - (S.card : ℝ)^3 : ℝ) : ℂ) := by
    push_cast <;> rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs] at h
  have hr : (0 : ℝ) < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (⟨0⟩ : Nonempty G))
  have hfactor : (Fintype.card G : ℝ) *
      ((returnCount S : ℝ) - (S.card : ℝ)^3 / (Fintype.card G : ℝ)) =
      (Fintype.card G : ℝ) * (returnCount S : ℝ) - (S.card : ℝ)^3 := by
    field_simp
  apply (mul_le_mul_left hr).mp
  calc
    _ = |(Fintype.card G : ℝ) *
        ((returnCount S : ℝ) - (S.card : ℝ)^3 / (Fintype.card G : ℝ))| := by
      rw [abs_mul, abs_of_pos hr]
    _ = _ := congrArg abs hfactor
    _ ≤ M * (Fintype.card G : ℝ) * (S.card : ℝ) := h
    _ = _ := by ring

end CryptoLean.SubsetFourier
