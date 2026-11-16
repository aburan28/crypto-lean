import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! Exact row-count bounds for adjacent-sum power profiles.
No rank, norm, lattice-success, or root-independence conclusion. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.ChainPowerBlocks

def adjacent (n : ℕ) (e : Fin (n+1) → ℕ) (i : Fin n) : ℕ :=
  e i.castSucc + e i.succ

theorem eq_of_head_adjacent (n : ℕ) (e f : Fin (n+1) → ℕ)
    (hhead : e 0 = f 0) (hprofile : adjacent n e = adjacent n f) : e=f := by
  funext i
  induction i using Fin.induction with
  | zero => exact hhead
  | succ i ih =>
    have h := congrFun hprofile i
    dsimp [adjacent] at h
    omega

theorem block_card_le (n t : ℕ) (S : Finset (Fin (n+1) → ℕ))
    (profile : Fin n → ℕ)
    (hhead : ∀ e ∈ S, e 0 ≤ t)
    (hprofile : ∀ e ∈ S, adjacent n e = profile) : S.card ≤ t+1 := by
  classical
  have h := Finset.card_le_card_of_injOn (s := S) (t := Finset.range (t+1))
    (fun e ↦ e 0) ?_ ?_
  · simpa only [Finset.card_range] using h
  · intro e he
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hhead e he))
  · intro e he f hf hsame
    exact eq_of_head_adjacent n e f hsame ((hprofile e he).trans (hprofile f hf).symm)

theorem shifted_block_card_le {μ : Type*} [DecidableEq μ]
    (n t : ℕ) (S : Finset ((Fin (n+1) → ℕ) × μ)) (menu : Finset μ)
    (shift : μ → Fin n → ℕ) (profile : Fin n → ℕ)
    (hmenu : ∀ r ∈ S, r.2 ∈ menu)
    (hhead : ∀ r ∈ S, r.1 0 ≤ t)
    (hprofile : ∀ r ∈ S, ∀ i, 2*adjacent n r.1 i + shift r.2 i = profile i) :
    S.card ≤ (t+1)*menu.card := by
  classical
  have h := Finset.card_le_card_of_injOn (s := S)
    (t := menu ×ˢ Finset.range (t+1)) (fun r ↦ (r.2, r.1 0)) ?_ ?_
  · simpa only [Finset.card_product, Finset.card_range, Nat.mul_comm] using h
  · intro r hr
    exact Finset.mem_product.mpr ⟨hmenu r hr,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hhead r hr))⟩
  · intro r hr s hs heq
    have hshift : r.2=s.2 := congrArg Prod.fst heq
    have hfirst : r.1 0=s.1 0 := congrArg Prod.snd heq
    have hpower : r.1=s.1 := by
      apply eq_of_head_adjacent n r.1 s.1 hfirst
      funext i
      have h1 := hprofile r hr i
      have h2 := hprofile s hs i
      rw [hshift] at h1
      omega
    exact Prod.ext hpower hshift

end CryptoLean.ChainPowerBlocks
