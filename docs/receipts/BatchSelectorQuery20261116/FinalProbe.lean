import CryptoLean.Group.TranslatedIntersections
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory CryptoLean
open scoped BigOperators

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (U V : H) (S : Finset H) (k : ℕ) (T : Fin k → H) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI : Finite W.Point := Finite.of_equiv
      (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
      W.nonsingularPointEquiv.symm
    letI : Fintype H := Fintype.ofFinite H
    letI : MeasurableSpace H := ⊤
    letI : DecidableEq H := Classical.decEq H
    let A := TranslatedIntersections.completionFilter (U + V) S
    ShiftRepresentations.acceptedCount U V S T =
      (∑ j : Fin k, if U + T j ∈ A then 1 else 0) ∧
    (∫ t, (if U + t ∈ S ∧ V - t ∈ S then (1 : ℝ) else 0)
      ∂uniformOn (Set.univ : Set H)) = (A.card : ℝ) / Fintype.card H ∧
    Var[fun t ↦ if U + t ∈ S ∧ V - t ∈ S then (1 : ℝ) else 0;
      uniformOn (Set.univ : Set H)] =
        ((A.card : ℝ) / Fintype.card H) * (1 - (A.card : ℝ) / Fintype.card H) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  letI : MeasurableSpace H := ⊤
  letI : DecidableEq H := Classical.decEq H
  exact ⟨TranslatedIntersections.acceptedCount_eq_sum U V S T,
    TranslatedIntersections.raw_tag_mean U V S,
    TranslatedIntersections.raw_tag_variance U V S⟩

example {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G)
    (hsym : ∀ P : G, P ∈ S ↔ -P ∈ S) :
    TranslatedIntersections.completionFilter 0 S = S :=
  TranslatedIntersections.zero_completionFilter S hsym
