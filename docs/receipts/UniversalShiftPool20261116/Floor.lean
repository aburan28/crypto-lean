import CryptoLean.Group.TranslatedIntersections
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

#check Finset.sum_image
#check Finset.sum_sub_distrib
#check Finset.sum_const
#check addOrderOf_dvd_iff_nsmul_eq_zero
#check Nat.le_of_dvd
#check Equiv.subtypePiEquivPi
#check Fintype.card_congr
#check Fintype.card_fun
#check Fintype.card_subtype_compl
#check Fintype.card_subtype
#check Finset.card_biUnion_le
#check Finset.card_lt_card
#check Finset.card_filter_le_iff

example {G : Type*} [AddCommGroup G] [DecidableEq G] (T : Finset G) (W : G) :
    (∑ P ∈ T.image (W - ·), P) = ∑ P ∈ T, (W - P) :=
  Finset.sum_image (fun _ _ _ _ h ↦ sub_right_inj.mp h)

example {G : Type*} [AddCommGroup G] (W : G) (n : ℕ) (h : n • W = 0) :
    addOrderOf W ∣ n := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h

open Classical in
example {H : Type*} [Fintype H] (Q : ℕ) (p : H → Prop) :
    Fintype.card {f : Fin Q → H // ∀ j, p (f j)} =
      Fintype.card (Fin Q → {x : H // p x}) :=
  Fintype.card_congr (Equiv.subtypePiEquivPi (β := fun _ : Fin Q ↦ H) (p := fun _ x ↦ p x))

example {I O : Type*} [DecidableEq O] (s : Finset I) (A : I → Finset O) :
    (s.biUnion A).card ≤ ∑ i ∈ s, (A i).card := Finset.card_biUnion_le
