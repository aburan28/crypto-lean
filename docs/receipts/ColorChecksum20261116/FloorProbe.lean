import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

#check Finset.sum_erase_add
#check Function.update_self
#check Function.update_of_ne
#check Finset.sum_nsmul_assoc
#check Finset.card_image_le
#check Fintype.card_fun

example {I G : Type*} [Fintype I] [DecidableEq I] [AddCommGroup G]
    (x : I → G) (i : I) :
    (∑ j ∈ (Finset.univ : Finset I).erase i, x j) + x i = ∑ j : I, x j :=
  Finset.sum_erase_add _ _ (Finset.mem_univ i)

example {J G : Type*} [Fintype J] [AddCommMonoid G] (u : J → ℕ) (g : G) :
    (∑ j : J, u j) • g = ∑ j : J, u j • g := by
  exact (Finset.sum_nsmul_assoc _ _ _).symm

example {I : Type*} [Fintype I] (K : ℕ) :
    Nat.card (I → Fin (K+1)) = (K+1)^Nat.card I := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_fun, Fintype.card_fin]

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) {I : Type*} [Fintype I] [DecidableEq I]
    (x : I → H) (i : I) :
    (∑ j ∈ (Finset.univ : Finset I).erase i, x j) + x i = ∑ j : I, x j :=
  Finset.sum_erase_add _ _ (Finset.mem_univ i)
