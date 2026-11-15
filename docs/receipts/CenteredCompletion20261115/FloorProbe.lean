import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

#check WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff
#check sub_left_inj
#check sub_right_inj
#check neg_sub
#check sub_eq_sub_iff_add_eq_add

example {G : Type*} [AddCommGroup G] (P Q S : G) :
    P - S = -(Q - S) ↔ P + Q = S + S := by
  rw [neg_sub, sub_eq_sub_iff_add_eq_add]

example {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
    (P Q S : W.Point) :
    (P - S).xRep = (Q - S).xRep ↔ P - S = Q - S ∨ P - S = -(Q - S) :=
  WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (P Q S : W.Point) :
    (P - S).xRep = (Q - S).xRep ↔ P - S = Q - S ∨ P - S = -(Q - S) :=
  WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff
