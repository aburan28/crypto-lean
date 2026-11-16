import CryptoLean.Polynomial.SmallLiftRigidity

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.SmallLiftRigidity CryptoLean.TwoChartCoefficients
open CryptoLean.CurveParameterElimination

namespace SmallLiftActual
variable {K : Type*} [Field K]

/-- The actual source anchors give exactly the common clearing equations. -/
theorem actual_anchor_clearing (a b τ σ scalar : K) :
    let c := scalar*projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 1).coeff 1)
    let d := scalar*projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 2).coeff 0)
    (2*scalar)*τ=-c ∧ (2*scalar)*σ=2*d+c := by
  simp only [(exact_source_anchors a b τ σ).2.1,
    (exact_source_anchors a b τ σ).2.2]
  constructor <;> ring

/-- Rationally lifted anchor parameters satisfy the denominator-cleared source
identity, for signed nonzero denominators without positivity assumptions. -/
theorem rational_reference (a x y w δ c d U V X W : ℚ) (hδ : δ ≠ 0) :
    clearedPrimitive a x y w δ c d U V X W =
      δ^5*primitive a 0 x y w (U+(-c/δ)*V) V (X+((2*d+c)/δ)*W) W := by
  apply cleared_scaling
  · field_simp
  · field_simp

/-- Simultaneous sign reversal of all three anchors preserves the same
rational chart and changes only the odd total-degree clearing scale. -/
theorem signed_reference (a x y w δ c d U V X W : ℤ) :
    clearedPrimitive a x y w (-δ) (-c) (-d) U V X W =
      -clearedPrimitive a x y w δ c d U V X W := by
  have hz : -δ*U-(-c)*V=(-1)*(δ*U-c*V) := by ring
  have ht : -δ*X+(2*(-d)+(-c))*W=(-1)*(δ*X+(2*d+c)*W) := by ring
  have hv : -δ*V=(-1)*(δ*V) := by ring
  have hw : -δ*W=(-1)*(δ*W) := by ring
  rw [clearedPrimitive,hz,ht,hv,hw,primitive_scaling]
  norm_num [clearedPrimitive]

/-- The exceptional identity holds as a polynomial in the remaining coordinate,
rather than only at a selected root. -/
theorem exceptional_remaining_polynomial (x y w δ c d U V W : ℚ)
    (hlinear : δ*U+(δ*(x+y)-c)*V=0) :
    clearedPrimitive (C (-(x^2+x*y+y^2))) (C x) (C y) (C w)
      (C δ) (C c) (C d) (C U) (C V) X (C W) = (0 : Polynomial ℚ) := by
  apply cleared_exceptional_zero
  · simp only [map_neg,map_add,map_pow,map_mul]
  · simpa only [map_mul,map_add,map_sub,Polynomial.C_0] using congrArg C hlinear

end SmallLiftActual
