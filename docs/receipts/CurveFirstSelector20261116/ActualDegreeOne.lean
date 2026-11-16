import CryptoLean.Polynomial.MixedDegreePivots

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.MixedDegreePivots CryptoLean.EndpointCoefficients

namespace CurveFirstActual
variable {K : Type*} [Field K]

theorem actual_endpoint_pivots (a b τ A B L : K) :
    let G := multiplier A B L τ * endpointInX (C a) (C b) X 0 1 (C τ)
    (G.coeff 3).coeff 2 = A ∧ (G.coeff 2).coeff 3 = B ∧
      (G.coeff 2).coeff 2 = L := by
  dsimp
  rw [← v2_as_endpoint]
  exact mixed_v2_pivots a b τ A B L

theorem x_branch_recovery (a b τ A B L c : K) (h₂ : (2 : K) ≠ 0)
    (hA : A ≠ 0) (hc : ((mixedUV a b τ A B L).coeff 3).coeff 0 = c) :
    τ = c/(2*A) := by
  apply (eq_div_iff (mul_ne_zero h₂ hA)).2
  rw [← hc,(mixed_uv_anchors a b τ A B L).1]
  ring

theorem y_branch_recovery (a b τ B L c : K) (h₂ : (2 : K) ≠ 0)
    (hB : B ≠ 0) (hc : ((mixedUV a b τ 0 B L).coeff 2).coeff 1 = c) :
    τ = (c+2*L)/(-2*B) := by
  apply (eq_div_iff (mul_ne_zero (neg_ne_zero.mpr h₂) hB)).2
  rw [← hc,mixed_anchor_branch_y]
  ring

theorem constant_branch_recovery (a b τ L c : K) (h₂ : (2 : K) ≠ 0)
    (hL : L ≠ 0) (hc : ((mixedUV a b τ 0 0 L).coeff 2).coeff 0 = c) :
    τ = c/(2*L) := by
  apply (eq_div_iff (mul_ne_zero h₂ hL)).2
  rw [← hc,mixed_anchor_branch_constant]
  ring

end CurveFirstActual
