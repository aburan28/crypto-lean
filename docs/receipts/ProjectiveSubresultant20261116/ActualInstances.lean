import CryptoLean.Polynomial.ProjectiveSubresultant

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.ProjectiveSubresultant CryptoLean.CurveParameterElimination

namespace SubresultantActual
variable {K : Type*} [Field K]

def actualCode (a b τ σ scalar : K) : Fin 4 → K :=
  ![scalar*coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 2).coeff 0) 0 2 1 0,
    scalar*coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 2).coeff 0) 0 1 1 1,
    scalar*coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 0).coeff 0) 1 1 0 1,
    scalar*coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 0).coeff 0) 1 0 0 2]

theorem actual_model_cover (a b τ σ scalar : K) (S : Finset K)
    (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hS : ∀ i, actualCode a b τ σ scalar i ∈ S) : (a,b) ∈ modelCandidates S := by
  have h := exact_source_anchors a b τ σ
  apply model_curve_cover S (actualCode a b τ σ scalar) scalar σ a b hl h₂ hS
  all_goals simp [actualCode,h.1,h.2.1,h.2.2.2.1,h.2.2.2.2,mul_comm,mul_left_comm]

theorem entire_source_nonzero (a b τ σ : K) : shiftedResidual a b τ σ ≠ 0 := by
  intro hz
  have h := (exact_source_anchors a b τ σ).1
  rw [hz] at h
  simp [coefficient4] at h

theorem original_s3_equivalence (a b x y w Z V T W : K)
    (hV : V ≠ 0) (hW : W ≠ 0) (hxy : x ≠ y) :
    (CryptoLean.Semaev.S3 a b x y (Z/V)=0 ∧ residual a b x y w Z V T W=0) ↔
      (CryptoLean.Semaev.S3 a b x y (Z/V)=0 ∧ CryptoLean.Semaev.S3 a b (Z/V) w (T/W)=0) := by
  have hf : first a b x y Z V=0 ↔ CryptoLean.Semaev.S3 a b x y (Z/V)=0 := by
    rw [first_clears_s3 a b x y Z V hV]
    simp [hV]
  have hg : adjacent a b w Z V T W=0 ↔ CryptoLean.Semaev.S3 a b (Z/V) w (T/W)=0 := by
    rw [adjacent_clears_s3 a b w Z V T W hV hW]
    simp [hV,hW]
  simpa only [hf,hg] using retained_residual_equiv a b x y w Z V T W hV hxy

theorem diagonal_remaining_polynomial (a b x w Z V W : K) (hV : V ≠ 0)
    (hfirst : first a b x x Z V=0) :
    residual (C a) (C b) (C x) (C x) (C w) (C Z) (C V) X (C W) = (0 : Polynomial K) := by
  have h := diagonal_identity (C a) (C b) (C x) (C w) (C Z) (C V) X (C W)
  have hf : first (C a) (C b) (C x) (C x) (C Z) (C V)=C (first a b x x Z V) := by
    simp [first,Polynomial.C_ofNat]
  rw [hf,hfirst,map_zero,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Polynomial.C_ne_zero.mpr hV)

theorem bounded_integer_source_cover (p T : ℕ) [Fact p.Prime]
    (a b τ σ scalar : ZMod p) (r : Fin 4 → ℤ)
    (hl : scalar ≠ 0) (h₂ : (2 : ZMod p) ≠ 0)
    (hr : ∀ i, (r i : ZMod p)=actualCode a b τ σ scalar i)
    (hT : ∀ i, (r i).natAbs ≤ T) :
    (a,b) ∈ modelCandidates (CryptoLean.FieldRectangles.intWindow (ZMod p) T) := by
  apply actual_model_cover a b τ σ scalar _ hl h₂
  intro i
  rw [← hr i]
  exact CryptoLean.FieldRectangles.mem_intWindow_of_bounds T (r i)
    (CryptoLean.ShortCoefficientWindows.integer_bounds_of_natAbs T (r i) (hT i))

end SubresultantActual
