import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite target-isolation counts from single/pair event cardinalities.
The only probability interpretation needed is uniform finite sampling. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.FiniteIsolation

theorem single_cover_count {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S : Finset E) (A : E → Finset O) (e : E) :
    (A e).card ≤ (A e \ (S.erase e).biUnion A).card +
      ∑ f ∈ S.erase e, (A e ∩ A f).card := by
  have hi : A e ∩ (S.erase e).biUnion A =
      (S.erase e).biUnion (fun f ↦ A e ∩ A f) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  have hsplit := Finset.card_sdiff_add_card_inter (A e) ((S.erase e).biUnion A)
  rw [hi] at hsplit
  have hb := Finset.card_biUnion_le (s := S.erase e) (t := fun f ↦ A e ∩ A f)
  omega

theorem target_events_disjoint {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S T : Finset E) (hT : T ⊆ S) (A : E → Finset O) :
    (T : Set E).PairwiseDisjoint (fun e ↦ A e \ (S.erase e).biUnion A) := by
  intro e he f hf hne
  apply Finset.disjoint_left.mpr
  intro w hwe hwf
  have hfS : f ∈ S.erase e := Finset.mem_erase.mpr ⟨Ne.symm hne, hT hf⟩
  exact (Finset.mem_sdiff.mp hwe).2
    (Finset.mem_biUnion.mpr ⟨f,hfS,(Finset.mem_sdiff.mp hwf).1⟩)

theorem target_union_count {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S T : Finset E) (hT : T ⊆ S) (A : E → Finset O) :
    (∑ e ∈ T, (A e).card) ≤
      (T.biUnion (fun e ↦ A e \ (S.erase e).biUnion A)).card +
        ∑ e ∈ T, ∑ f ∈ S.erase e, (A e ∩ A f).card := by
  have hs := Finset.sum_le_sum (fun e (_he : e ∈ T) ↦ single_cover_count S A e)
  rw [Finset.sum_add_distrib,
    ← Finset.card_biUnion (target_events_disjoint S T hT A)] at hs
  exact hs

theorem scaled_target_isolation {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S T : Finset E) (hT : T ⊆ S) (A : E → Finset O) (B C : ℕ)
    (hsingle : ∀ e ∈ T, B*(A e).card = C)
    (hpair : ∀ e ∈ T, ∀ f ∈ S.erase e, B^2*(A e ∩ A f).card ≤ C) :
    T.card*C*B ≤
      B^2*(T.biUnion (fun e ↦ A e \ (S.erase e).biUnion A)).card +
        T.card*(S.card-1)*C := by
  have hleft : B^2*(∑ e ∈ T, (A e).card) = T.card*C*B := by
    rw [Finset.mul_sum]
    calc
      _ = ∑ _e ∈ T, C*B := by
        apply Finset.sum_congr rfl
        intro e he
        calc
          B^2*(A e).card = B*(B*(A e).card) := by ring
          _ = B*C := by rw [hsingle e he]
          _ = C*B := Nat.mul_comm _ _
      _ = _ := by simp [Nat.mul_assoc]
  have hper (e : E) (he : e ∈ T) :
      B^2*(∑ f ∈ S.erase e, (A e ∩ A f).card) ≤ (S.card-1)*C := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _f ∈ S.erase e, C := Finset.sum_le_sum (fun f hf ↦ hpair e he f hf)
      _ = _ := by simp [Finset.card_erase_of_mem (hT he)]
  have hright : B^2*(∑ e ∈ T, ∑ f ∈ S.erase e, (A e ∩ A f).card) ≤
      T.card*(S.card-1)*C := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _e ∈ T, (S.card-1)*C := Finset.sum_le_sum hper
      _ = _ := by simp [Nat.mul_assoc]
  have h := Nat.mul_le_mul_left (B^2) (target_union_count S T hT A)
  rw [Nat.mul_add, hleft] at h
  exact h.trans (Nat.add_le_add_left hright _)

theorem half_scaled_target_isolation {E O : Type*} [DecidableEq E] [DecidableEq O]
    (S T : Finset E) (hT : T ⊆ S) (A : E → Finset O) (B C : ℕ)
    (hsingle : ∀ e ∈ T, B*(A e).card = C)
    (hpair : ∀ e ∈ T, ∀ f ∈ S.erase e, B^2*(A e ∩ A f).card ≤ C)
    (hsize : 2*S.card ≤ B) (hB : 0 < B) :
    T.card*C ≤ 2*B*(T.biUnion (fun e ↦ A e \ (S.erase e).biUnion A)).card := by
  have h := scaled_target_isolation S T hT A B C hsingle hpair
  have hrem : 2*(S.card-1) ≤ B := by omega
  have hsmall := Nat.mul_le_mul_left (T.card*C) hrem
  have hdoubled := Nat.mul_le_mul_left 2 h
  apply (mul_le_mul_iff_left₀ hB).mp
  nlinarith

end CryptoLean.FiniteIsolation
