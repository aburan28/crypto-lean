import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-! Reflection of centered finite supports and the inherited torsion obstruction. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.TranslatedSupports

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem sum_reflection (W : G) (T : Finset G) :
    (∑ P ∈ T.image (W - ·), P) = T.card • W - ∑ P ∈ T, P := by
  rw [Finset.sum_image (fun _ _ _ _ h ↦ sub_right_inj.mp h),
    Finset.sum_sub_distrib, Finset.sum_const]

theorem centered_reflection_nsmul (W : G) (S T : Finset G)
    (hS : ∑ P ∈ S, P = 0) (hT : ∑ P ∈ T, P = 0)
    (hreflect : S = T.image (W - ·)) : T.card • W = 0 := by
  have h := sum_reflection W T
  rw [← hreflect, hS, hT, sub_zero] at h
  exact h.symm

theorem centered_reflection_ne (W : G) (S T : Finset G)
    (hS : ∑ P ∈ S, P = 0) (hT : ∑ P ∈ T, P = 0)
    (hpos : 0 < T.card) (hsmall : T.card < addOrderOf W) :
    S ≠ T.image (W - ·) := by
  intro h
  have hd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    (centered_reflection_nsmul W S T hS hT h)
  exact (not_le_of_gt hsmall) (Nat.le_of_dvd hpos hd)

theorem sum_symmetric_union (T : Finset G)
    (hdis : Disjoint T (T.image Neg.neg)) :
    (∑ P ∈ T ∪ T.image Neg.neg, P) = 0 := by
  rw [Finset.sum_union hdis, Finset.sum_image (fun _ _ _ _ h ↦ neg_injective h)]
  rw [Finset.sum_neg_distrib, add_neg_cancel]

end CryptoLean.TranslatedSupports
