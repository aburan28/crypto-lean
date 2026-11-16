import CryptoLean.Polynomial.TwoChartCoefficients

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.TwoChartCoefficients CryptoLean.CurveParameterElimination

namespace TwoChartActual
variable {K : Type*} [Field K]

theorem source_scalar_decode (a b τ σ scalar : K) (hs : scalar ≠ 0)
    (h₂ : (2 : K) ≠ 0) :
    τ = -(scalar*projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 1).coeff 1)) /
      (2*scalar) ∧
    σ = (scalar*projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 2).coeff 0)) /
      scalar-τ := by
  rw [(exact_source_anchors a b τ σ).2.1,(exact_source_anchors a b τ σ).2.2]
  exact recover_two_parameters scalar τ σ _ _ hs h₂ rfl rfl

theorem source_nonzero (a b τ σ : K) : shiftedModel a b τ σ ≠ 0 := by
  intro hz
  have h := (exact_source_anchors a b τ σ).1
  rw [hz] at h
  simp [projectiveAnchor] at h

theorem scalar_anchor_nonzero (a b τ σ scalar : K) (hs : scalar ≠ 0) :
    scalar*projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 2).coeff 1) ≠ 0 := by
  rw [(exact_source_anchors a b τ σ).1,mul_one]
  exact hs

theorem entire_model_independent_b (a b τ σ : K) :
    shiftedModel a b τ σ = shiftedModel a 0 τ σ := by
  simp only [shiftedModel,leafModel,inXY,inX,primitive_independent_b]

theorem exceptional_raw_polynomial (b x y w V W : K) :
    primitive (C (-(x^2+x*y+y^2))) (C b) (C x) (C y) (C w)
      (C (-(x+y)*V)) (C V) X (C W) = (0 : Polynomial K) := by
  simpa only [map_neg,map_add,map_mul,map_pow] using
    exceptional_raw_zero (C b) (C x) (C y) (C w) (C V) X (C W)

end TwoChartActual
