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
    simp [hn]
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

omit [Fintype G] in
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

theorem second_moment_row (a : Fin m → Fin b) (hm : 0 < m) :
    (∑ c : Fin m → Fin b, ∑ x : (Fin m × Fin b) → G, hit a x * hit c x) *
      (Fintype.card G)^2 =
      Fintype.card G ^ (m*b) * (Fintype.card G + (b^m - 1)) := by
  classical
  have hd : (∑ x : (Fin m × Fin b) → G, hit a x * hit a x) *
      (Fintype.card G)^2 = Fintype.card G ^ (m*b) * Fintype.card G := by
    simp_rw [← pow_two, hit_sq]
    calc
      _ = ((∑ x : (Fin m × Fin b) → G, hit a x) * Fintype.card G) *
          Fintype.card G := by ring
      _ = _ := by rw [single_event_count (G := G) a hm]
  rw [Finset.sum_mul, ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  have ho : (∑ c ∈ (Finset.univ : Finset (Fin m → Fin b)).erase a,
      (∑ x : (Fin m × Fin b) → G, hit a x * hit c x) * (Fintype.card G)^2) =
      (b^m - 1) * Fintype.card G ^ (m*b) := by
    calc
      _ = ∑ _c ∈ (Finset.univ : Finset (Fin m → Fin b)).erase a,
          Fintype.card G ^ (m*b) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact joint_event_count a c (Ne.symm (Finset.ne_of_mem_erase hc))
      _ = _ := by simp
  rw [ho, hd]
  ring

theorem second_moment (hm : 0 < m) :
    (∑ x : (Fin m × Fin b) → G, relationCount x ^ 2) * (Fintype.card G)^2 =
      Fintype.card G ^ (m*b) * b^m * (Fintype.card G + (b^m - 1)) := by
  classical
  have hexp (x : (Fin m × Fin b) → G) : relationCount x ^ 2 =
      ∑ a : Fin m → Fin b, ∑ c : Fin m → Fin b, hit a x * hit c x := by
    rw [pow_two, relationCount, Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (f := fun x c => hit _ x * hit c x)]
  rw [Finset.sum_mul]
  simp_rw [second_moment_row (G := G) _ hm]
  simp
  ring

omit [Fintype G] in
theorem relationCount_ne_zero_iff (x : (Fin m × Fin b) → G) :
    relationCount x ≠ 0 ↔ ∃ a : Fin m → Fin b, tupleSum a x = 0 := by
  classical
  simp [relationCount, hit]

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

/-- Exact unconditioned coverage for independent uniform entries in an actual
finite additive commutative group. Dividing by the assignment-space cardinality
gives probability at least `b^m / (card G + b^m - 1)`. -/
theorem coverage_count [Fintype G] (hm : 0 < m) (hb : 0 < b) :
    b^m * Fintype.card G ^ (m*b) ≤
      (Fintype.card G + b^m - 1) *
        Nat.card {x : (Fin m × Fin b) → G // ∃ a : Fin m → Fin b, tupleSum a x = 0} := by
  classical
  let S := ∑ x : (Fin m × Fin b) → G, relationCount x
  let U := ∑ x : (Fin m × Fin b) → G, relationCount x ^ 2
  let H := (Finset.univ.filter (fun x : (Fin m × Fin b) → G => relationCount x ≠ 0)).card
  let r := Fintype.card G
  let L := b^m
  let N := r^(m*b)
  have hfirst : S*r = L*N := first_moment (G := G) hm
  have hsecond : U*r^2 = N*L*(r+(L-1)) := second_moment (G := G) hm
  have hcs : S^2 ≤ H*U := support_cauchy_schwarz (relationCount (G := G) (m := m) (b := b))
  have hscaled : (L*N)^2 ≤ H * (N*L*(r+(L-1))) := by
    calc
      (L*N)^2 = S^2*r^2 := by rw [← hfirst]; ring
      _ ≤ (H*U)*r^2 := Nat.mul_le_mul_right _ hcs
      _ = H * (N*L*(r+(L-1))) := by rw [mul_assoc, hsecond]
  have hr : 0 < r := Fintype.card_pos_iff.mpr ⟨0⟩
  have hL : 0 < L := Nat.pow_pos hb
  have hN : 0 < N := Nat.pow_pos hr
  have hcancel : L*N ≤ H*(r+(L-1)) := by
    apply Nat.le_of_mul_le_mul_right (c := L*N) _ (Nat.mul_pos hL hN)
    convert hscaled using 1 <;> ring
  have hcard : H = Nat.card {x : (Fin m × Fin b) → G //
      ∃ a : Fin m → Fin b, tupleSum a x = 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    change (Finset.univ.filter _).card = (Finset.univ.filter _).card
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact relationCount_ne_zero_iff x
  have hdenom : r+(L-1) = r+L-1 := by omega
  change L*N ≤ (r+L-1)*_
  rw [← hcard, ← hdenom, mul_comm]
  exact hcancel

end CryptoLean.PartiteCoverage
