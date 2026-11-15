import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

#check Finset.min'
#check Finset.min'_mem
#check Finset.min'_le
#check Finset.card_union_le
#check Equiv.piCongrRight
#check Equiv.addLeft
#check Equiv.subtypeEquivOfSubtype
#check Nat.card_congr

example {K : Type*} [LinearOrder K] (s : Finset K) (h : s.Nonempty) :
    s.min' h ∈ s := Finset.min'_mem s h

example {K : Type*} [LinearOrder K] (s : Finset K) (x : K) (hx : x ∈ s) :
    s.min' ⟨x, hx⟩ ≤ x := Finset.min'_le s x hx

example {G : Type*} [AddGroup G] (U : G) (b : ℕ) :
    ((Fin b → G) × (Fin b → G)) ≃ ((Fin b → G) × (Fin b → G)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ ↦ Equiv.addLeft U)).trans
    ((Equiv.prodComm _ _).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.piCongrRight fun _ ↦ (Equiv.addLeft U).symm)))

example {Ω : Type*} (e : Ω ≃ Ω) (P : Ω → Prop) :
    Nat.card {x : Ω // P (e x)} = Nat.card {x : Ω // P x} :=
  Nat.card_congr (e.subtypeEquivOfSubtype (p := P))

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (b : ℕ) :
    Finite ((Fin b → H) × (Fin b → H)) ∧
      Nat.card ((Fin b → H) × (Fin b → H)) = (Nat.card H) ^ (2 * b) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  constructor
  · infer_instance
  · simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin, ← pow_add, two_mul]

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p)) (P : W.Point) :
    p * ((-P).xRep 1).val + ((-P).xRep 0).val =
      p * (P.xRep 1).val + (P.xRep 0).val := by
  simp only [WeierstrassCurve.Affine.Point.xRep_neg]
