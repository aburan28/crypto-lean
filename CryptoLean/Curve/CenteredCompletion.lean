import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Exact pair completion using the existing normalized, infinity-aware
x representative after a group translation. No Riemann--Roch construction
or search algorithm is asserted by this coordinate interface. -/
set_option autoImplicit false

namespace CryptoLean.CenteredCompletion

variable {F : Type*} [Field F] [DecidableEq F]
variable {W : WeierstrassCurve.Affine F}

/-- Centered x fibers are the diagonal and the prescribed pair-sum fiber. -/
theorem centered_xRep_eq_iff (P Q S : W.Point) :
    (P - S).xRep = (Q - S).xRep ↔ P = Q ∨ P + Q = S + S := by
  rw [WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff, sub_left_inj,
    neg_sub, sub_eq_sub_iff_add_eq_add]

/-- For distinct records and an explicit half target, key collisions are
exactly pair completions. The existence/construction of the half is separate. -/
theorem centered_completion_iff (P Q S T : W.Point) (hPQ : P ≠ Q)
    (hcenter : S + S = T) :
    (P - S).xRep = (Q - S).xRep ↔ P + Q = T := by
  rw [centered_xRep_eq_iff, hcenter]
  exact or_iff_right hPQ

end CryptoLean.CenteredCompletion
