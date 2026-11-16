import CryptoLean.Curve.LineIncidence
import CryptoLean.Polynomial.ProjectiveProducts
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Quadratic-character carry for actual Weierstrass addition.
The curve identities are inherited from Mathlib; input chart exclusions
are explicit. Infinity, inverse pairs and doubling require their own cases. -/
set_option autoImplicit false
noncomputable section
open Polynomial

namespace CryptoLean.CharacterCarry

/-- Evaluation of the existing chord/tangent addition polynomial at an anchor. -/
theorem line_norm {F : Type*} [Field F] [DecidableEq F]
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

theorem quadratic_norm {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) {x₁ x₂ y₁ y₂ a b : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) (hA : W.Equation a b)
    (ha₁ : x₁ ≠ a) (ha₂ : x₂ ≠ a) :
    let s := W.slope x₁ x₂ y₁ y₂
    let L := (WeierstrassCurve.Affine.linePolynomial x₁ y₁ s).eval a
    quadraticChar F (W.addX x₁ x₂ s-a) =
      quadraticChar F (x₁-a) * quadraticChar F (x₂-a) *
        quadraticChar F ((b-L)*(W.negY a b-L)) :=
  ProjectiveProducts.quadratic_transfer _ _ _ _ _
    (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr ha₂) (line_norm W h₁ h₂ hxy hA)

/-- In the nonvertical anchor chart, the common secant scale is a square. -/
theorem quadratic_key {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) {x₁ x₂ y₁ y₂ a b : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (h12 : x₁ ≠ x₂) (hA : W.Equation a b) (ha₁ : x₁ ≠ a) (ha₂ : x₂ ≠ a) :
    quadraticChar F (W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)-a) =
      quadraticChar F (x₁-a) * quadraticChar F (x₂-a) *
        quadraticChar F (((y₁-b)/(x₁-a)-(y₂-b)/(x₂-a))*
          ((y₁-W.negY a b)/(x₁-a)-(y₂-W.negY a b)/(x₂-a))) := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := fun h ↦ h12 h.1
  have hc := quadratic_norm W h₁ h₂ hxy hA ha₁ ha₂
  dsimp only at hc
  simp only [WeierstrassCurve.Affine.linePolynomial, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, W.slope_of_X_ne h12] at hc
  rw [ProjectiveProducts.secant_key x₁ y₁ x₂ y₂ a b h12 ha₁ ha₂,
    ProjectiveProducts.secant_key x₁ y₁ x₂ y₂ a (W.negY a b) h12 ha₁ ha₂] at hc
  let s := (x₁-a)*(x₂-a)/(x₁-x₂)
  have hs : s ≠ 0 := div_ne_zero
    (mul_ne_zero (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr ha₂)) (sub_ne_zero.mpr h12)
  have hsquare (u v : F) : quadraticChar F (s*u*(s*v)) = quadraticChar F (u*v) := by
    calc
      quadraticChar F (s*u*(s*v)) = quadraticChar F (s^2*(u*v)) := congrArg _ (by ring)
      _ = quadraticChar F (u*v) := by rw [map_mul, quadraticChar_sq_one' hs, one_mul]
  rw [hsquare] at hc
  simpa only [W.slope_of_X_ne h12] using hc

end CryptoLean.CharacterCarry
