import CryptoLean.Group.PartiteCoverage
import Mathlib.Data.Fintype.BigOperators
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open scoped BigOperators

#check AddMonoidHom.card_fiber_eq_of_mem_range
#check AddSubgroup.card_ker_mul_card_of_surjective
#check Fintype.card_le_of_surjective
#check Fintype.card_sigma
#check CryptoLean.PartiteCoverage.tupleSum_surjective

example {H G : Type*} [AddGroup H] [AddGroup G] [Fintype H] [DecidableEq G]
    (f : H →+ G) (hsur : Function.Surjective f) (g : G) :
    (Finset.univ.filter fun x ↦ f x = g).card =
      (Finset.univ.filter fun x ↦ f x = 0).card :=
  AddMonoidHom.card_fiber_eq_of_mem_range f (hsur g) (hsur 0)

example {H G : Type*} [AddGroup H] [AddGroup G]
    (f : H →+ G) (hsur : Function.Surjective f) :
    Nat.card f.ker * Nat.card G = Nat.card H :=
  AddSubgroup.card_ker_mul_card_of_surjective hsur

example {Ω W : Type*} [Fintype Ω] [Fintype W] (p : W → Ω)
    (hp : Function.Surjective p) : Fintype.card Ω ≤ Fintype.card W :=
  Fintype.card_le_of_surjective p hp

example {A C H G : Type*} [Fintype A] [Fintype C] [Fintype H] [Fintype G]
    [DecidableEq G] (F : A → Finset G) (f : C → H → G) :
    Fintype.card (Σ a : A, Σ g : {g : G // g ∈ F a}, Σ c : C, {x : H // f c x = g.val}) =
      ∑ a : A, ∑ g : {g : G // g ∈ F a}, ∑ c : C, Fintype.card {x : H // f c x = g.val} := by
  simp only [Fintype.card_sigma]

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) {s b : ℕ} (c : Fin s → Fin b) (hs : 0 < s) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI : Finite W.Point := Finite.of_equiv
      (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
      W.nonsingularPointEquiv.symm
    letI : Fintype H := Fintype.ofFinite H
    letI : DecidableEq H := Classical.decEq H
    0 < Fintype.card H ∧ ∀ g : H,
      (Finset.univ.filter (fun x ↦ CryptoLean.PartiteCoverage.tupleSum (G := H) c x = g)).card =
        (Finset.univ.filter (fun x ↦ CryptoLean.PartiteCoverage.tupleSum (G := H) c x = 0)).card := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  letI : DecidableEq H := Classical.decEq H
  refine ⟨Fintype.card_pos_iff.mpr ⟨0⟩, fun g ↦ ?_⟩
  exact AddMonoidHom.card_fiber_eq_of_mem_range (CryptoLean.PartiteCoverage.tupleSum c)
    (CryptoLean.PartiteCoverage.tupleSum_surjective c hs g)
    (CryptoLean.PartiteCoverage.tupleSum_surjective c hs 0)
