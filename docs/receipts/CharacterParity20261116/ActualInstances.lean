import CryptoLean.Curve.CharacterCarry
import CryptoLean.Group.BilinearSketch
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    {x₁ x₂ y₁ y₂ a b : ZMod p}
    (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (h12 : x₁ ≠ x₂) (hA : W.Equation a b) (ha₁ : x₁ ≠ a) (ha₂ : x₂ ≠ a) :
    quadraticChar (ZMod p)
      ((WeierstrassCurve.Affine.Point.some _ _ h₁ +
        WeierstrassCurve.Affine.Point.some _ _ h₂).xRep 0-a) =
      quadraticChar (ZMod p) (x₁-a) * quadraticChar (ZMod p) (x₂-a) *
        quadraticChar (ZMod p) (((y₁-b)/(x₁-a)-(y₂-b)/(x₂-a))*
          ((y₁-W.negY a b)/(x₁-a)-(y₂-W.negY a b)/(x₂-a))) := by
  simpa only [WeierstrassCurve.Affine.Point.add_of_X_ne h12,
    WeierstrassCurve.Affine.Point.xRep_some, Matrix.cons_val_zero] using
      CryptoLean.CharacterCarry.quadratic_key W h₁.left h₂.left h12 hA ha₁ ha₂

example (p : ℕ) [Fact p.Prime] (a : ZMod p) (m : ℕ) (g : (ZMod p)[X]) :
    (taylor a ((X-C a)^m*g)).coeff m = g.eval a :=
  CryptoLean.ProjectiveProducts.taylor_strip_root a m g

example {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I J (ZMod 2)) (i : I) (j : J) (h : M i j = 1) :
    Nat.card (J → ZMod 2) ≤ 2 * Nat.card {c : J → ZMod 2 // M.mulVec c ≠ 0} :=
  CryptoLean.BilinearSketch.matrix_half_count M i j h

open Classical in
example (p : ℕ) [Fact p.Prime] {I : Type*} (s : Finset I) (u : I → ZMod p) (a : ZMod p) :
    (taylor a (∏ j ∈ s, (X-C (u j)))).coeff (s.filter (fun j ↦ u j = a)).card =
      ∏ j ∈ s.filter (fun j ↦ u j ≠ a), (a-u j) := by
  convert
    CryptoLean.ProjectiveProducts.indexed_taylor_nonzero s u a using 1 <;> congr

open Classical in
example (p : ℕ) [Fact p.Prime] {I : Type*} (s : Finset I) (u : I → ZMod p) (B : I → Prop)
    (h : ∀ j ∈ s, ¬B j → u j ≠ 0) :
    (∏ j ∈ s.filter (fun j ↦ u j ≠ 0), u j) /
        (∏ j ∈ (s.filter (fun j ↦ u j ≠ 0)).filter B, u j) =
      ∏ j ∈ s.filter (fun j ↦ ¬B j), u j := by
  convert
    CryptoLean.ProjectiveProducts.nonzero_product_correction s u B h using 1; congr
