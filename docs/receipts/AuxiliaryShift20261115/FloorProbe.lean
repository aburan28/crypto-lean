import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Data.Finsupp.Single
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

#check variance_sum_pi
#check integral_comp_eval
#check integral_indicator_one
#check variance_eq_sub
#check MemLp.of_discrete
#check Finite.of_equiv
#check Finsupp.single_left_inj

example {R : Type*} [Ring R] [Nontrivial R] {k : ℕ} (j l : Fin k) :
    Finsupp.single j (1 : R) - Finsupp.single l 1 = 0 ↔ j = l := by
  rw [sub_eq_zero, Finsupp.single_left_inj one_ne_zero]

example {G : Type*} [AddCommGroup G] [Fintype G]
    [MeasurableSpace G] [DiscreteMeasurableSpace G] (f : G → ℝ) (k : ℕ) :
    Var[∑ i : Fin k, fun t : Fin k → G ↦ f (t i);
      Measure.pi (fun _ : Fin k ↦ uniformOn (Set.univ : Set G))] =
      ∑ _ : Fin k, Var[f; uniformOn (Set.univ : Set G)] := by
  exact variance_sum_pi (fun _ ↦ MemLp.of_discrete)

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) (U : H) (S : Finset H) (k : ℕ) :
    letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    letI : Finite W.Point := Finite.of_equiv
      (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
      W.nonsingularPointEquiv.symm
    letI : Fintype H := Fintype.ofFinite H
    letI : MeasurableSpace H := ⊤
    let f : H → ℝ := fun g ↦ if U + g ∈ S then 1 else 0
    Var[∑ i : Fin k, fun t : Fin k → H ↦ f (t i);
      Measure.pi (fun _ : Fin k ↦ uniformOn (Set.univ : Set H))] =
      ∑ _ : Fin k, Var[f; uniformOn (Set.univ : Set H)] := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  letI : MeasurableSpace H := ⊤
  dsimp only
  exact variance_sum_pi (ι := Fin k) (Ω := fun _ : Fin k ↦ H)
    (mΩ := fun _ ↦ ⊤)
    (μ := fun _ : Fin k ↦ uniformOn (Set.univ : Set H))
    (X := fun _ g ↦ if U + g ∈ S then 1 else 0)
    (fun _ ↦ MemLp.of_discrete)

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (P : W.Point) (I : Finset (ZMod p)) :
    (-P).xRep 0 ∈ I ↔ P.xRep 0 ∈ I := by
  rw [WeierstrassCurve.Affine.Point.xRep_neg]
