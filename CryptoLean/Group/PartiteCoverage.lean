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
  change (∑ i : Fin m, (Pi.single (i0, c i0) g : (Fin m × Fin b) → G) (i, a i)) = _
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

section Counting
variable [Fintype G]

noncomputable def hit (a : Fin m → Fin b) (x : (Fin m × Fin b) → G) : ℕ := by
  classical
  exact if tupleSum a x = 0 then 1 else 0

noncomputable def relationCount (x : (Fin m × Fin b) → G) : ℕ :=
  ∑ a : Fin m → Fin b, hit a x

theorem single_event_count (a : Fin m → Fin b) (hm : 0 < m) :
    (∑ x : (Fin m × Fin b) → G, hit a x) * Fintype.card G =
      Fintype.card G ^ (m*b) := by
  classical
  have hk : Nat.card (tupleSum (G := G) a).ker =
      ∑ x : (Fin m × Fin b) → G, hit a x := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {x : (Fin m × Fin b) → G // tupleSum a x = 0} = _
    rw [Fintype.card_subtype, Finset.card_filter]
    rfl
  simpa only [hk, Nat.card_eq_fintype_card] using single_kernel_card (G := G) a hm

theorem joint_event_count (a c : Fin m → Fin b) (hac : a ≠ c) :
    (∑ x : (Fin m × Fin b) → G, hit a x * hit c x) * (Fintype.card G)^2 =
      Fintype.card G ^ (m*b) := by
  classical
  have hk : Nat.card ((tupleSum (G := G) a).prod (tupleSum c)).ker =
      ∑ x : (Fin m × Fin b) → G, hit a x * hit c x := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {x : (Fin m × Fin b) → G //
      (tupleSum a x, tupleSum c x) = (0,0)} = _
    rw [Fintype.card_subtype, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hit, Prod.mk.injEq]
    split_ifs <;> simp_all
  simpa only [hk, Nat.card_eq_fintype_card] using joint_kernel_card (G := G) a c hac

theorem hit_sq (a : Fin m → Fin b) (x : (Fin m × Fin b) → G) :
    hit a x ^ 2 = hit a x := by
  classical
  simp only [hit]
  split_ifs <;> rfl

theorem first_moment (hm : 0 < m) :
    (∑ x : (Fin m × Fin b) → G, relationCount x) * Fintype.card G =
      b^m * Fintype.card G ^ (m*b) := by
  classical
  simp only [relationCount]
  rw [Finset.sum_comm, Finset.sum_mul]
  simp_rw [single_event_count (G := G) _ hm]
  simp

end Counting

/-- The finite Cauchy--Schwarz support inequality, with exact integer counts. -/
theorem support_cauchy_schwarz {Ω : Type*} [Fintype Ω] (f : Ω → ℕ) :
    (∑ x, f x)^2 ≤ (Finset.univ.filter (fun x => f x ≠ 0)).card * ∑ x, f x^2 := by
  classical
  have hmul : (∑ x, (if f x = 0 then 0 else 1) * f x) = ∑ x, f x := by
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with hx <;> simp [hx]
  have hcard : (∑ x, (if f x = 0 then 0 else 1 : ℕ)^2) =
      (Finset.univ.filter (fun x => f x ≠ 0)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => if f x = 0 then 0 else 1) f
  rwa [hmul, hcard] at h

end CryptoLean.PartiteCoverage
