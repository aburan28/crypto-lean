import CryptoLean.Group.RankThreshold
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section

open CryptoLean

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (b : ℕ) (hb : 0 < b) (U V : H) (hzero : U + V = 0) :
    (Nat.card H) ^ (2 * b) ≤ 2 * Nat.card
      {ω : RankThreshold.Pools H b //
        RankThreshold.pairedSuccess
          (fun g : H ↦ p * (g.val.xRep 1).val + (g.val.xRep 0).val) hb U V ω} := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  exact RankThreshold.raw_card_le_twice_paired _ hb U V hzero
    (fun g ↦ by simp only [AddSubgroup.coe_neg, WeierstrassCurve.Affine.Point.xRep_neg])

example {R : Type*} [Ring R] [Nontrivial R] {b : ℕ} (j l : Fin b) :
    ShiftRepresentations.leftVector (R := R) j + ShiftRepresentations.rightVector l =
      ShiftRepresentations.originalVector ↔ j = l :=
  ShiftRepresentations.vector_sum_eq_original_iff j l

example {R : Type*} [Ring R] [Nontrivial R] {b : ℕ} (j : Fin b) :
    ShiftRepresentations.leftVector (R := R) j + ShiftRepresentations.rightVector j ≠ 0 :=
  ShiftRepresentations.vector_sum_ne_zero j j
