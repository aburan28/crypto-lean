import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

#check quadraticChar_sq_one
#check map_mul

example {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (x y z l r : F) (hx : x ≠ 0) (hy : y ≠ 0) (h : l*r=x*y*z) :
    quadraticChar F z = quadraticChar F x * quadraticChar F y * quadraticChar F (l*r) := by
  have hc := congrArg (quadraticChar F) h
  simp only [map_mul] at hc
  calc
    quadraticChar F z = (quadraticChar F x ^ 2 * quadraticChar F y ^ 2) *
        quadraticChar F z := by rw [quadraticChar_sq_one hx, quadraticChar_sq_one hy]; simp
    _ = quadraticChar F x * quadraticChar F y * quadraticChar F (l*r) := by
      rw [map_mul, hc]
      ring

example {F : Type*} [Field F] (x1 y1 x2 y2 a b : F)
    (h12 : x1 ≠ x2) (h1 : x1 ≠ a) (h2 : x2 ≠ a) :
    b-((y1-y2)/(x1-x2)*(a-x1)+y1) =
      ((x1-a)*(x2-a)/(x1-x2))*((y1-b)/(x1-a)-(y2-b)/(x2-a)) := by
  field_simp [sub_ne_zero.mpr h12, sub_ne_zero.mpr h1, sub_ne_zero.mpr h2]
  ring
