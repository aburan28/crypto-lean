import CryptoLean.Group.ShortlistCompletion
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators

#check Pi.evalAddMonoidHom
#check AddMonoidHom.fst
#check AddMonoidHom.snd
#check AddMonoidHom.prod
#check Finset.card_biUnion
#check Finset.card_biUnion_le

example {G H : Type*} [AddGroup G] [AddGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hs : Function.Surjective f) (h : H) :
    Nat.card {g : G // f g = h} * Nat.card H = Nat.card G :=
  CryptoLean.ShortlistCompletion.fiber_card_mul f hs h

example {I J H : Type*} [AddCommGroup H] (i : I) (j : J)
    (r : I → H) (c : J → H) :
    (((Pi.evalAddMonoidHom (fun _ : I ↦ H) i).comp (AddMonoidHom.fst (I → H) (J → H)) +
       (Pi.evalAddMonoidHom (fun _ : J ↦ H) j).comp (AddMonoidHom.snd (I → H) (J → H)))
      (r,c) : H) = r i+c j := rfl

example (ell : ℕ) {I J : Type*} (i : I) (j : J)
    (r : I → Fin ell → ZMod 2) (c : J → Fin ell → ZMod 2) :
    (((Pi.evalAddMonoidHom (fun _ : I ↦ Fin ell → ZMod 2) i).comp
         (AddMonoidHom.fst (I → Fin ell → ZMod 2) (J → Fin ell → ZMod 2)) +
       (Pi.evalAddMonoidHom (fun _ : J ↦ Fin ell → ZMod 2) j).comp
         (AddMonoidHom.snd (I → Fin ell → ZMod 2) (J → Fin ell → ZMod 2))) (r,c) : Fin ell → ZMod 2) = r i+c j := rfl

example {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S : Finset E) (A : E → Finset O) (e : E) :
    (A e).card ≤ (A e \ (S.erase e).biUnion A).card +
      ∑ f ∈ S.erase e, (A e ∩ A f).card := by
  have hi : A e ∩ (S.erase e).biUnion A =
      (S.erase e).biUnion (fun f ↦ A e ∩ A f) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  have hsplit := Finset.card_sdiff_add_card_inter (A e) ((S.erase e).biUnion A)
  rw [hi] at hsplit
  have hb := Finset.card_biUnion_le (s := S.erase e) (t := fun f ↦ A e ∩ A f)
  omega
