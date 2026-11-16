import CryptoLean.Curve.LineIncidence
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false
noncomputable section
open Polynomial

#check WeierstrassCurve.Affine.addPolynomial_slope
#check WeierstrassCurve.Affine.C_addPolynomial
#check Polynomial.evalEval

example {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) {x₁ x₂ y₁ y₂ a b : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) (hA : W.Equation a b) :
    let s := W.slope x₁ x₂ y₁ y₂
    let L := (WeierstrassCurve.Affine.linePolynomial x₁ y₁ s).eval a
    (b-L)*(W.negY a b-L) = (x₁-a)*(x₂-a)*(W.addX x₁ x₂ s-a) := by
  dsimp only
  have hf := congrArg (Polynomial.eval a) (W.addPolynomial_slope h₁ h₂ hxy)
  have hn := congrArg (fun f : Polynomial (Polynomial F) ↦ f.evalEval a b)
    (W.C_addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂))
  simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C] at hf
  have heq : W.polynomial.evalEval a b = 0 := hA
  simp [WeierstrassCurve.Affine.negPolynomial, heq, Polynomial.evalEval_C] at hn
  rw [hf] at hn
  simp only [WeierstrassCurve.Affine.negY]
  linear_combination -hn
