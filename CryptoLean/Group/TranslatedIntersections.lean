import CryptoLean.Group.ShiftMoments

/-! The actual two-gate event at an arbitrary subtotal. No zero-target or
filter symmetry is needed; all existing frozen shift laws remain unchanged. -/
set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CryptoLean.TranslatedIntersections

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {k : ℕ}

def completionFilter (W : G) (S : Finset G) : Finset G :=
  S.filter (fun P ↦ W - P ∈ S)

theorem mem_completionFilter (W P : G) (S : Finset G) :
    P ∈ completionFilter W S ↔ P ∈ S ∧ W - P ∈ S :=
  Finset.mem_filter

theorem both_gates_iff (U V t : G) (S : Finset G) :
    (U + t ∈ S ∧ V - t ∈ S) ↔ U + t ∈ completionFilter (U + V) S := by
  rw [mem_completionFilter]
  simp only [add_sub_add_left_eq_sub]

theorem acceptedCount_eq_sum (U V : G) (S : Finset G) (T : Fin k → G) :
    ShiftRepresentations.acceptedCount U V S T =
      ∑ j : Fin k, if U + T j ∈ completionFilter (U + V) S then 1 else 0 := by
  change (Finset.univ.filter (fun j ↦ U + T j ∈ S ∧ V - T j ∈ S)).card = _
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  simp only [both_gates_iff]

theorem indicator_eq (U V : G) (S : Finset G) :
    (fun t : G ↦ if U + t ∈ S ∧ V - t ∈ S then (1 : ℝ) else 0) =
      (fun t ↦ if U + t ∈ completionFilter (U + V) S then (1 : ℝ) else 0) := by
  funext t
  simp only [both_gates_iff]

theorem zero_completionFilter (S : Finset G) (hsym : ∀ P : G, P ∈ S ↔ -P ∈ S) :
    completionFilter 0 S = S := by
  ext P
  rw [mem_completionFilter]
  simp only [zero_sub, ← hsym P, and_self]

section Moments

variable [Fintype G] [MeasurableSpace G] [DiscreteMeasurableSpace G]

theorem raw_tag_mean (U V : G) (S : Finset G) :
    (∫ t, (if U + t ∈ S ∧ V - t ∈ S then (1 : ℝ) else 0)
      ∂uniformOn (Set.univ : Set G)) =
        ((completionFilter (U + V) S).card : ℝ) / Fintype.card G := by
  rw [indicator_eq]
  exact ShiftRepresentations.shifted_hit_mean U _

theorem raw_tag_variance (U V : G) (S : Finset G) :
    Var[fun t ↦ if U + t ∈ S ∧ V - t ∈ S then (1 : ℝ) else 0;
      uniformOn (Set.univ : Set G)] =
        (((completionFilter (U + V) S).card : ℝ) / Fintype.card G) *
          (1 - ((completionFilter (U + V) S).card : ℝ) / Fintype.card G) := by
  rw [indicator_eq]
  exact ShiftRepresentations.shifted_hit_variance U _

end Moments

end CryptoLean.TranslatedIntersections
