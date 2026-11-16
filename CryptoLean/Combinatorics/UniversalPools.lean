import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/-! Finite product pools simultaneously hitting an arbitrary finite family.
Only uniform finite-cardinality interpretation is needed by consumers. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.UniversalPools

variable {H I : Type*} [Fintype H] [DecidableEq H]

def missPools (Q : ℕ) (A : Finset H) : Finset (Fin Q → H) := by
  classical
  exact Finset.univ.filter (fun pool ↦ ∀ j, pool j ∉ A)

theorem fixed_miss_count (Q : ℕ) (A : Finset H) :
    (missPools Q A).card = (Fintype.card H - A.card)^Q := by
  classical
  have h := Fintype.card_congr
    (Equiv.subtypePiEquivPi (β := fun _ : Fin Q ↦ H) (p := fun _ x ↦ x ∉ A))
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl,
    Fintype.card_subtype] at h
  simpa only [Fintype.card_subtype, missPools, Finset.filter_mem_eq_inter,
    Finset.univ_inter] using h

def badPools (Q : ℕ) (S : Finset I) (A : I → Finset H) : Finset (Fin Q → H) := by
  classical
  exact S.biUnion (fun i ↦ missPools Q (A i))

theorem mem_badPools (Q : ℕ) (S : Finset I) (A : I → Finset H) (pool : Fin Q → H) :
    pool ∈ badPools Q S A ↔ ∃ i ∈ S, ∀ j, pool j ∉ A i := by
  classical
  simp only [badPools, Finset.mem_biUnion, missPools, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem miss_union_bound (Q : ℕ) (S : Finset I) (A : I → Finset H) :
    (badPools Q S A).card ≤ ∑ i ∈ S, (Fintype.card H - (A i).card)^Q := by
  classical
  calc
    _ ≤ ∑ i ∈ S, (missPools Q (A i)).card := Finset.card_biUnion_le
    _ = _ := Finset.sum_congr rfl (fun i _ ↦ fixed_miss_count Q (A i))

theorem universal_miss_bound (Q a : ℕ) (S : Finset I) (A : I → Finset H)
    (hA : ∀ i ∈ S, a ≤ (A i).card) :
    (badPools Q S A).card ≤ S.card * (Fintype.card H - a)^Q := by
  calc
    _ ≤ ∑ i ∈ S, (Fintype.card H - (A i).card)^Q := miss_union_bound Q S A
    _ ≤ ∑ _i ∈ S, (Fintype.card H - a)^Q := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      exact hA i hi
    _ = _ := by simp

theorem exists_universal_pool (Q a : ℕ) (S : Finset I) (A : I → Finset H)
    (hA : ∀ i ∈ S, a ≤ (A i).card)
    (hcap : S.card * (Fintype.card H - a)^Q < (Fintype.card H)^Q) :
    ∃ pool : Fin Q → H, ∀ i ∈ S, ∃ j, pool j ∈ A i := by
  classical
  have hcount : (badPools Q S A).card < (Finset.univ : Finset (Fin Q → H)).card := by
    simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using
      (universal_miss_bound Q a S A hA).trans_lt hcap
  obtain ⟨pool, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcount
  refine ⟨pool, ?_⟩
  intro i hi
  by_contra! hno
  exact hp ((mem_badPools Q S A pool).mpr ⟨i, hi, hno⟩)

end CryptoLean.UniversalPools
