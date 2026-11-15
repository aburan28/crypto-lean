import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-! Finite secant-fibre counts on existing Weierstrass-curve semantics.
Consumer: crypto's fixed, point-independent slope partial-join assessment,
prospective scope b1e8ecdd26. No point-generation or relation-search algorithm. -/
set_option autoImplicit false
namespace CryptoLean.LineIncidence
open Polynomial
variable {F : Type*} [Field F]

theorem addPolynomial_natDegree (W : WeierstrassCurve.Affine F) (x y ℓ : F) :
    (W.addPolynomial x y ℓ).natDegree = 3 := by
  rw [WeierstrassCurve.Affine.addPolynomial_eq, Polynomial.natDegree_neg]
  exact Cubic.natDegree_of_a_ne_zero' one_ne_zero

theorem addPolynomial_eval (W : WeierstrassCurve.Affine F) (x y ℓ t : F) :
    (W.addPolynomial x y ℓ).eval t = W.polynomial.evalEval t (ℓ*(t-x)+y) := by
  simp [WeierstrassCurve.Affine.addPolynomial, WeierstrassCurve.Affine.polynomial,
    WeierstrassCurve.Affine.linePolynomial, Polynomial.evalEval]

theorem line_root_iff (W : WeierstrassCurve.Affine F) (x y ℓ t : F) :
    (W.addPolynomial x y ℓ).IsRoot t ↔ W.Equation t (ℓ*(t-x)+y) := by
  rw [Polynomial.IsRoot, addPolynomial_eval, WeierstrassCurve.Affine.Equation]

theorem line_x_card [Fintype F] (W : WeierstrassCurve.Affine F) (x y ℓ : F) :
    Nat.card {t : F // W.Equation t (ℓ*(t-x)+y)} ≤ 3 := by
  classical
  let p := W.addPolynomial x y ℓ
  have hp : p ≠ 0 := by
    intro hz
    have hd := addPolynomial_natDegree W x y ℓ
    change p.natDegree = 3 at hd
    simp [hz] at hd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter (fun t : F => W.Equation t (ℓ*(t-x)+y))).val ⊆
      p.roots := by
    intro t ht
    rw [Polynomial.mem_roots hp, line_root_iff]
    exact (Finset.mem_filter.mp ht).2
  exact (Polynomial.card_le_degree_of_subset_roots hsub).trans (by
    rw [addPolynomial_natDegree])

theorem other_line_x_card [Fintype F] (W : WeierstrassCurve.Affine F)
    (x y ℓ : F) (hP : W.Equation x y) :
    Nat.card {t : F // t ≠ x ∧ W.Equation t (ℓ*(t-x)+y)} ≤ 2 := by
  classical
  let s := Finset.univ.filter (fun t : F => W.Equation t (ℓ*(t-x)+y))
  have hx : x ∈ s := by simpa [s] using hP
  have hs : s.card ≤ 3 := by
    simpa only [s, Nat.card_eq_fintype_card, Fintype.card_subtype] using line_x_card W x y ℓ
  have he : Nat.card {t : F // t ≠ x ∧ W.Equation t (ℓ*(t-x)+y)} = (s.erase x).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp [s, and_comm]
  rw [he, Finset.card_erase_of_mem hx]
  omega

/-- Counting actual affine curve points: projection to x is injective on a
nonvertical line, so at most two other points share the prescribed secant. -/
theorem other_line_point_card [Fintype F] (W : WeierstrassCurve.Affine F)
    (x y ℓ : F) (hP : W.Equation x y) :
    Nat.card {q : F × F // q.1 ≠ x ∧ W.Equation q.1 q.2 ∧ q.2 = ℓ*(q.1-x)+y} ≤ 2 := by
  classical
  let f : {q : F × F // q.1 ≠ x ∧ W.Equation q.1 q.2 ∧ q.2 = ℓ*(q.1-x)+y} →
      {t : F // t ≠ x ∧ W.Equation t (ℓ*(t-x)+y)} := fun q =>
    ⟨q.val.1, q.property.1, q.property.2.2 ▸ q.property.2.1⟩
  have hf : Function.Injective f := by
    intro q q' h
    have hx : q.val.1 = q'.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Prod.ext hx
    rw [q.property.2.2, q'.property.2.2, hx]
  exact (by simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf).trans
    (other_line_x_card W x y ℓ hP)

end CryptoLean.LineIncidence
