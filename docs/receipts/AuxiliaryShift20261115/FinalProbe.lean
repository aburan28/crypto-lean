import CryptoLean.Group.ShiftMoments
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory CryptoLean.ShiftRepresentations

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (U V : H) (S : Finset H) (k : ℕ)
    (hzero : U + V = 0) (hsym : ∀ g : H, g ∈ S ↔ -g ∈ S) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI : Finite W.Point := Finite.of_equiv
      (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
      W.nonsingularPointEquiv.symm
    letI : Fintype H := Fintype.ofFinite H
    letI : MeasurableSpace H := ⊤
    let μ := Measure.pi (fun _ : Fin k ↦ uniformOn (Set.univ : Set H))
    let δ : ℝ := S.card / Fintype.card H
    (∫ T : Fin k → H, (acceptedCount U V S T : ℝ) ∂μ) = (k : ℝ) * δ ∧
    Var[fun T : Fin k → H ↦ (acceptedCount U V S T : ℝ); μ] = (k : ℝ) * δ * (1 - δ) ∧
    (∫ T : Fin k → H, (acceptedCount U V S T : ℝ) ^ 2 ∂μ) =
      (k : ℝ) * δ + (k : ℝ) * ((k : ℝ) - 1) * δ ^ 2 := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  letI : MeasurableSpace H := ⊤
  exact ⟨acceptedCount_mean U V S hzero hsym,
    acceptedCount_variance U V S hzero hsym, acceptedCount_second_moment U V S hzero hsym⟩

example {G : Type*} [AddCommGroup G] {k : ℕ} (U V : G) (T : Fin k → G)
    (hzero : U + V = 0) (j : Fin k) : V - T j = -(U + T j) :=
  right_shift_eq_neg_left U V (T j) hzero
