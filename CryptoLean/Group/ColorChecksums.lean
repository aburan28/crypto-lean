import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! A common additive checksum target for every one-per-color tuple forces
constant weights inside each color. Such checksums see color totals only. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.ColorChecksums

theorem weights_eq_of_common_target {I J G : Type*} [Fintype I] [AddCommGroup G]
    (weights : I → J → G) (target : G)
    (htarget : ∀ c : I → J, ∑ i : I, weights i (c i) = target)
    (i : I) (j k : J) : weights i j = weights i k := by
  classical
  let c : I → J := fun _ ↦ j
  let d : I → J := Function.update c i k
  have heq := (htarget c).trans (htarget d).symm
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at heq
  have herase : (∑ x ∈ (Finset.univ : Finset I).erase i, weights x (c x)) =
      ∑ x ∈ (Finset.univ : Finset I).erase i, weights x (d x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [show d x = c x from Function.update_of_ne (Finset.ne_of_mem_erase hx) _ _]
  rw [herase] at heq
  simpa only [c, d, Function.update_self] using add_left_cancel heq

theorem common_target_iff {I J G : Type*} [Fintype I] [AddCommGroup G]
    (weights : I → J → G) (j0 : J) :
    (∃ target : G, ∀ c : I → J, ∑ i : I, weights i (c i) = target) ↔
      ∀ i : I, ∀ j k : J, weights i j = weights i k := by
  constructor
  · rintro ⟨target, htarget⟩ i j k
    exact weights_eq_of_common_target weights target htarget i j k
  · intro hweights
    refine ⟨∑ i : I, weights i j0, fun c ↦ ?_⟩
    exact Finset.sum_congr rfl fun i _ ↦ hweights i (c i) j0

theorem checksum_eq_profile {I J G : Type*} [Fintype I] [Fintype J] [AddCommMonoid G]
    (weights : I → G) (u : I → J → ℕ) :
    (∑ i : I, ∑ j : J, u i j • weights i) =
      ∑ i : I, (∑ j : J, u i j) • weights i := by
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_nsmul_assoc _ _ _

theorem checksum_image_card_le {I J G : Type*} [Fintype I] [Fintype J] [AddCommMonoid G]
    [DecidableEq G]
    (V : Finset (I → J → ℕ)) (weights : I → G) (K : ℕ)
    (hcap : ∀ u ∈ V, ∀ i : I, (∑ j : J, u i j) ≤ K) :
    (V.image (fun u : I → J → ℕ ↦ ∑ i : I, ∑ j : J, u i j • weights i)).card ≤
      (K+1)^Fintype.card I := by
  classical
  let profileHash : (I → Fin (K+1)) → G := fun d ↦ ∑ i : I, (d i).val • weights i
  have hsubset : V.image (fun u ↦ ∑ i : I, ∑ j : J, u i j • weights i) ⊆
      Finset.univ.image profileHash := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
    let d : I → Fin (K+1) := fun i ↦ ⟨∑ j : J, u i j, Nat.lt_succ_of_le (hcap u hu i)⟩
    refine Finset.mem_image.mpr ⟨d, Finset.mem_univ d, ?_⟩
    exact (checksum_eq_profile weights u).symm
  calc
    _ ≤ (Finset.univ.image profileHash).card := Finset.card_le_card hsubset
    _ ≤ (Finset.univ : Finset (I → Fin (K+1))).card := Finset.card_image_le
    _ = (K+1)^Fintype.card I := by simp

end CryptoLean.ColorChecksums
