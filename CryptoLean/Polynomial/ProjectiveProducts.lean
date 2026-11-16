import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-! Indexed cross-difference resultants and projective scaling. Indexing
retains repetitions; no squarefree or distinct-point hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators

namespace CryptoLean.ProjectiveProducts

/-- The first coefficient surviving translation of a known repeated root.
No characteristic or factorial-invertibility hypothesis is used. -/
theorem taylor_strip_root {R : Type*} [CommRing R] (a : R) (m : ℕ) (g : R[X]) :
    (taylor a ((X-C a)^m*g)).coeff m = g.eval a := by
  have hs : taylor a (X-C a) = (X : R[X]) := by simp [taylor_apply]
  rw [taylor_mul, taylor_pow, hs]
  simpa using (coeff_X_pow_mul (taylor a g) m 0)

open Classical in
/-- Strip every indexed occurrence of an evaluation key, including multiplicities. -/
theorem indexed_taylor_nonzero {R I : Type*} [CommRing R]
    (s : Finset I) (u : I → R) (a : R) :
    (taylor a (∏ j ∈ s, (X-C (u j)))).coeff (s.filter (fun j ↦ u j = a)).card =
      ∏ j ∈ s.filter (fun j ↦ u j ≠ a), (a-u j) := by
  classical
  have he : (∏ j ∈ s.filter (fun j ↦ u j = a), (X-C (u j))) =
      (X-C a : R[X])^(s.filter (fun j ↦ u j = a)).card := by
    calc
      _ = ∏ j ∈ s.filter (fun j ↦ u j = a), (X-C a : R[X]) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = _ := Finset.prod_const _
  rw [← Finset.prod_filter_mul_prod_filter_not s (fun j ↦ u j = a) (fun j ↦ (X-C (u j))),
    he, taylor_strip_root]
  simp [Polynomial.eval_prod]

open Classical in
/-- Remove the forbidden nonzero factors after zero stripping. Every retained
factor is assumed nonzero; the correction denominator is proved nonzero. -/
theorem nonzero_product_correction {F I : Type*} [Field F]
    (s : Finset I) (u : I → F) (B : I → Prop) (hu : ∀ j ∈ s, ¬B j → u j ≠ 0) :
    (∏ j ∈ s.filter (fun j ↦ u j ≠ 0), u j) /
        (∏ j ∈ (s.filter (fun j ↦ u j ≠ 0)).filter B, u j) =
      ∏ j ∈ s.filter (fun j ↦ ¬B j), u j := by
  classical
  have he : (s.filter (fun j ↦ u j ≠ 0)).filter (fun j ↦ ¬B j) =
      s.filter (fun j ↦ ¬B j) := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, hu j h.1 h.2⟩, h.2⟩
  have hd : (∏ j ∈ (s.filter (fun j ↦ u j ≠ 0)).filter B, u j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
  apply (div_eq_iff hd).mpr
  have hs := Finset.prod_filter_mul_prod_filter_not (s.filter (fun j ↦ u j ≠ 0)) B u
  rw [he] at hs
  exact hs.symm.trans (mul_comm _ _)

/-- A norm identity with two nonzero input factors transfers to characters. -/
theorem quadratic_transfer {F : Type*} [Field F] [Fintype F] [DecidableEq F]
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

/-- Scalar secant evaluation in a slope-key chart. -/
theorem secant_key {F : Type*} [Field F] (x1 y1 x2 y2 a b : F)
    (h12 : x1 ≠ x2) (h1 : x1 ≠ a) (h2 : x2 ≠ a) :
    b-((y1-y2)/(x1-x2)*(a-x1)+y1) =
      ((x1-a)*(x2-a)/(x1-x2))*((y1-b)/(x1-a)-(y2-b)/(x2-a)) := by
  field_simp [sub_ne_zero.mpr h12, sub_ne_zero.mpr h1, sub_ne_zero.mpr h2]
  ring

theorem indexed_resultant {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (u : I → F) (v : J → F) :
    (∏ i : I, (X-C (u i))).resultant (∏ j : J, (X-C (v j))) =
      ∏ i : I, ∏ j : J, (u i-v j) := by
  classical
  rw [Polynomial.resultant_prod_left]
  · simp [Polynomial.eval_prod]
  · simp
  · exact le_rfl

theorem scaled_difference_product {F I J : Type*} [Field F] [Fintype I] [Fintype J]
    (u a : I → F) (v b : J → F) :
    (∏ i : I, ∏ j : J, a i*b j*(u i-v j)) =
      (∏ i : I, a i)^Fintype.card J * (∏ j : J, b j)^Fintype.card I *
        (∏ i : I, (X-C (u i))).resultant (∏ j : J, (X-C (v j))) := by
  classical
  rw [indexed_resultant]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]

end CryptoLean.ProjectiveProducts
