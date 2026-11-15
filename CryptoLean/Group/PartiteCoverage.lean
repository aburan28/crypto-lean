import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Counting partite zero-sum relations in an actual finite additive group.
The coverage endpoint is developed from surjective tuple-sum maps; no root
enumeration, native computation or relation-search algorithm is introduced. -/
set_option autoImplicit false
namespace CryptoLean.PartiteCoverage
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] {m b : ℕ}

def tupleSum (a : Fin m → Fin b) : ((Fin m × Fin b) → G) →+ G where
  toFun x := ∑ i : Fin m, x (i, a i)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem tupleSum_spike (a c : Fin m → Fin b) (i0 : Fin m) (g : G) :
    tupleSum a (Pi.single (i0, c i0) g) = if a i0 = c i0 then g else 0 := by
  classical
  change (∑ i : Fin m, Pi.single (i0, c i0) g (i, a i)) = _
  rw [Finset.sum_eq_single i0]
  · simp [Pi.single_apply]
  · intro i _ hi
    have hn : (i, a i) ≠ (i0, c i0) := by
      intro heq
      exact hi (congrArg Prod.fst heq)
    simp [Pi.single_apply, hn]
  · simp

theorem tupleSum_surjective (a : Fin m → Fin b) (hm : 0 < m) :
    Function.Surjective (tupleSum (G := G) a) := by
  intro g
  let i0 : Fin m := ⟨0, hm⟩
  refine ⟨Pi.single (i0, a i0) g, ?_⟩
  simpa using tupleSum_spike a a i0 g

theorem jointSum_surjective (a c : Fin m → Fin b) (hac : a ≠ c) :
    Function.Surjective ((tupleSum (G := G) a).prod (tupleSum c)) := by
  classical
  obtain ⟨i0, hi⟩ := Function.ne_iff.mp hac
  rintro ⟨u,v⟩
  refine ⟨Pi.single (i0, a i0) u + Pi.single (i0, c i0) v, ?_⟩
  apply Prod.ext
  · change tupleSum a (Pi.single (i0, a i0) u + Pi.single (i0, c i0) v) = u
    rw [map_add, tupleSum_spike, tupleSum_spike]
    simp [hi]
  · change tupleSum c (Pi.single (i0, a i0) u + Pi.single (i0, c i0) v) = v
    rw [map_add, tupleSum_spike, tupleSum_spike]
    simp [Ne.symm hi]

theorem single_kernel_card (a : Fin m → Fin b) (hm : 0 < m) :
    Nat.card (tupleSum (G := G) a).ker * Nat.card G = Nat.card G ^ (m*b) := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective (tupleSum_surjective (G := G) a hm)
  simpa only [Nat.card_fun, Nat.card_prod, Nat.card_fin] using h

theorem joint_kernel_card (a c : Fin m → Fin b) (hac : a ≠ c) :
    Nat.card ((tupleSum (G := G) a).prod (tupleSum c)).ker * (Nat.card G)^2 =
      Nat.card G ^ (m*b) := by
  have h := AddSubgroup.card_ker_mul_card_of_surjective (jointSum_surjective (G := G) a c hac)
  simpa only [Nat.card_fun, Nat.card_prod, Nat.card_fin, pow_two] using h

end CryptoLean.PartiteCoverage
