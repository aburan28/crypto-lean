import Mathlib.Data.Finset.Max
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import CryptoLean.Group.ShiftRepresentations

/-! Finite marker-rank survival with full raw pool multiplicities and ties.
The swap below is a counting equivalence, not a replacement input sampler. -/
set_option autoImplicit false

noncomputable section

namespace CryptoLean.RankThreshold

abbrev Pools (G : Type*) (b : ℕ) := (Fin b → G) × (Fin b → G)

section Minimum

variable {K : Type*} [LinearOrder K] {b : ℕ}

def minimum (hb : 0 < b) (f : Fin b → K) : K :=
  (Finset.univ.image f).min'
    ⟨f ⟨0, hb⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩

theorem minimum_spec (hb : 0 < b) (f : Fin b → K) :
    (∀ i, minimum hb f ≤ f i) ∧ ∃ i, f i = minimum hb f := by
  constructor
  · intro i
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem f (Finset.mem_univ i))
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp
      (Finset.min'_mem (Finset.univ.image f) _)
    exact ⟨i, hi⟩

end Minimum

section Swap

variable {G : Type*} [AddGroup G] {K : Type*} [LinearOrder K] {b : ℕ}

def poolSwap (U : G) : Pools G b ≃ Pools G b :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ ↦ Equiv.addLeft U)).trans
    ((Equiv.prodComm _ _).trans
      (Equiv.prodCongr (Equiv.refl _)
        (Equiv.piCongrRight fun _ ↦ (Equiv.addLeft U).symm)))

theorem poolSwap_apply (U : G) (ω : Pools G b) :
    poolSwap U ω = (fun j ↦ U + ω.2 j, fun i ↦ -U + ω.1 i) := rfl

def success (κ : G → K) (hb : 0 < b) (U : G) (ω : Pools G b) : Prop :=
  minimum hb (fun j ↦ κ (U + ω.2 j)) ≤ minimum hb (fun i ↦ κ (ω.1 i))

theorem success_iff (κ : G → K) (hb : 0 < b) (U : G) (ω : Pools G b) :
    success κ hb U ω ↔
      minimum hb (fun j ↦ κ (U + ω.2 j)) ≤ minimum hb (fun i ↦ κ (ω.1 i)) := Iff.rfl

theorem success_tag_iff (κ : G → K) (hb : 0 < b) (U : G) (ω : Pools G b) :
    success κ hb U ω ↔ ∃ j, ∀ i, κ (U + ω.2 j) ≤ κ (ω.1 i) := by
  rw [success_iff]
  constructor
  · intro h
    obtain ⟨j, hj⟩ := (minimum_spec hb (fun j ↦ κ (U + ω.2 j))).2
    exact ⟨j, fun i ↦ hj.trans_le (h.trans ((minimum_spec hb (fun i ↦ κ (ω.1 i))).1 i))⟩
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := (minimum_spec hb (fun i ↦ κ (ω.1 i))).2
    exact ((minimum_spec hb (fun j ↦ κ (U + ω.2 j))).1 j).trans ((hj i).trans_eq hi)

theorem success_swap_iff (κ : G → K) (hb : 0 < b) (U : G) (ω : Pools G b) :
    success κ hb U (poolSwap U ω) ↔
      minimum hb (fun i ↦ κ (ω.1 i)) ≤ minimum hb (fun j ↦ κ (U + ω.2 j)) := by
  simp only [success_iff, poolSwap_apply, add_neg_cancel_left]

theorem success_or_swap (κ : G → K) (hb : 0 < b) (U : G) (ω : Pools G b) :
    success κ hb U ω ∨ success κ hb U (poolSwap U ω) := by
  rw [success_iff, success_swap_iff]
  exact le_total _ _

theorem raw_card_le_twice_success [Fintype G] (κ : G → K) (hb : 0 < b) (U : G) :
    Nat.card (Pools G b) ≤ 2 * Nat.card {ω : Pools G b // success κ hb U ω} := by
  classical
  let s := Finset.univ.filter (success κ hb U)
  let t := Finset.univ.filter (fun ω ↦ success κ hb U (poolSwap U ω))
  have hcover : s ∪ t = Finset.univ := by
    ext ω
    simp only [s, t, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact success_or_swap κ hb U ω
  have hcard : t.card = s.card := by
    have h := Nat.card_congr ((poolSwap (b := b) U).subtypeEquivOfSubtype (p := success κ hb U))
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  calc
    Nat.card (Pools G b) = (Finset.univ : Finset (Pools G b)).card := by
      rw [Nat.card_eq_fintype_card, Finset.card_univ]
    _ = (s ∪ t).card := congrArg Finset.card hcover.symm
    _ ≤ s.card + t.card := Finset.card_union_le s t
    _ = 2 * Nat.card {ω : Pools G b // success κ hb U ω} := by
      rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
      exact (two_mul s.card).symm

end Swap

section Paired

variable {G : Type*} [AddCommGroup G] {K : Type*} [LinearOrder K] {b : ℕ}

def pairedSuccess (κ : G → K) (hb : 0 < b) (U V : G) (ω : Pools G b) : Prop :=
  ∃ j, κ (U + ω.2 j) ≤ minimum hb (fun i ↦ κ (ω.1 i)) ∧
    κ (V - ω.2 j) ≤ minimum hb (fun i ↦ κ (ω.1 i))

theorem pairedSuccess_iff (κ : G → K) (hb : 0 < b) (U V : G) (ω : Pools G b) :
    pairedSuccess κ hb U V ω ↔
      ∃ j, κ (U + ω.2 j) ≤ minimum hb (fun i ↦ κ (ω.1 i)) ∧
        κ (V - ω.2 j) ≤ minimum hb (fun i ↦ κ (ω.1 i)) := Iff.rfl

theorem pairedSuccess_iff_success (κ : G → K) (hb : 0 < b) (U V : G)
    (hzero : U + V = 0) (hκ : ∀ g, κ (-g) = κ g) (ω : Pools G b) :
    pairedSuccess κ hb U V ω ↔ success κ hb U ω := by
  rw [pairedSuccess_iff, success_tag_iff]
  simp only [ShiftRepresentations.right_shift_eq_neg_left U V _ hzero, hκ, and_self]
  apply exists_congr
  intro j
  constructor
  · intro h i
    exact h.trans ((minimum_spec hb (fun i ↦ κ (ω.1 i))).1 i)
  · intro h
    obtain ⟨i, hi⟩ := (minimum_spec hb (fun i ↦ κ (ω.1 i))).2
    exact (h i).trans_eq hi

theorem raw_card_le_twice_paired [Fintype G] (κ : G → K) (hb : 0 < b) (U V : G)
    (hzero : U + V = 0) (hκ : ∀ g, κ (-g) = κ g) :
    (Nat.card G) ^ (2 * b) ≤
      2 * Nat.card {ω : Pools G b // pairedSuccess κ hb U V ω} := by
  have h := raw_card_le_twice_success κ hb U
  simp only [Pools, Nat.card_prod, Nat.card_fun, Nat.card_fin, ← pow_add, ← two_mul] at h
  simpa only [pairedSuccess_iff_success κ hb U V hzero hκ] using h

end Paired

end CryptoLean.RankThreshold
