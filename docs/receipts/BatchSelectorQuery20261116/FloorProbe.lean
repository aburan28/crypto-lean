import CryptoLean.Group.ShiftMoments
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory CryptoLean.ShiftRepresentations

#check add_sub_add_left_eq_sub
#check Finset.card_filter
#check shifted_hit_mean
#check shifted_hit_variance

example {G : Type*} [AddCommGroup G] (U V t : G) :
    (U + V) - (U + t) = V - t := add_sub_add_left_eq_sub V t U

example {G : Type*} [AddCommGroup G] [DecidableEq G] (U V t : G) (S : Finset G) :
    (U + t ∈ S ∧ V - t ∈ S) ↔ U + t ∈ S.filter (fun P ↦ (U + V) - P ∈ S) := by
  simp only [Finset.mem_filter, add_sub_add_left_eq_sub]

example {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G] (U V : G) (S : Finset G) :
    (∫ t, (if U + t ∈ S.filter (fun P ↦ (U + V) - P ∈ S) then (1 : ℝ) else 0)
      ∂uniformOn (Set.univ : Set G)) =
        ((S.filter (fun P ↦ (U + V) - P ∈ S)).card : ℝ) / Fintype.card G :=
  shifted_hit_mean U _

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (U V : H) (S : Finset H) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI : Finite W.Point := Finite.of_equiv
      (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
      W.nonsingularPointEquiv.symm
    letI : Fintype H := Fintype.ofFinite H
    letI : MeasurableSpace H := ⊤
    letI : DecidableEq H := Classical.decEq H
    (∫ t, (if U + t ∈ S.filter (fun P ↦ (U + V) - P ∈ S) then (1 : ℝ) else 0)
      ∂uniformOn (Set.univ : Set H)) =
        ((S.filter (fun P ↦ (U + V) - P ∈ S)).card : ℝ) / Fintype.card H := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  letI : MeasurableSpace H := ⊤
  letI : DecidableEq H := Classical.decEq H
  exact shifted_hit_mean U _
