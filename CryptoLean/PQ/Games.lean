import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

/-!
# Games over uniform coins

The smallest kernel needed to state and prove cryptographic reductions as Lean theorems.
An *experiment* is a Boolean function of its coins `ω : Ω`, where `Ω` is a finite type
and the coins are drawn uniformly. Every sampler used by ML-KEM is of this form: the
matrix `A` is uniform (random-oracle model of `SampleNTT`), and the centred binomial
distribution `B_η` is the image of `2η` uniform bits (`CBD.lean`), so "sample from
`B_η`" is "draw uniform coins and apply a function".

* `pr f`: the probability that `f` holds on uniform coins, `#{ω | f ω} / #Ω` (in `ℚ`).
* `pr_equiv`: reindexing the coins by a bijection does not change the probability. This
  is the one rule every game hop below uses ("these two games sample the same thing").
* `pr_nonneg`, `pr_le_one`: probabilities lie in `[0, 1]`.
* `pr_mono`: a smaller event has smaller probability (used for failure bounds).

Inheritance (lean-instance-gate): the sum is Mathlib's `Finset.sum`, reindexing is
`Equiv.sum_comp`, and `#Ω` is preserved by `Fintype.card_congr`. Counting measure on a
finite type is used directly rather than `PMF.uniformOfFintype`, because every game here
is a finite uniform experiment and the counting form keeps game equalities definitional.
-/

set_option autoImplicit false

namespace CryptoLean.PQ

open Finset

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

/-- Probability that `f` holds when `ω : Ω` is drawn uniformly. -/
def pr (f : Ω → Bool) : ℚ :=
  (∑ ω, if f ω then (1 : ℚ) else 0) / Fintype.card Ω

/-- **Change of variables.** Reindexing uniform coins along a bijection preserves every
probability. -/
theorem pr_equiv (e : Ω ≃ Ω') (f : Ω' → Bool) : pr (f ∘ e) = pr f := by
  unfold pr
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e (fun x => if f x then (1 : ℚ) else 0)

/-- Pointwise-equal experiments under a bijection have equal probability. -/
theorem pr_eq_of_equiv (e : Ω ≃ Ω') (f : Ω → Bool) (g : Ω' → Bool)
    (h : ∀ ω, g (e ω) = f ω) : pr f = pr g := by
  have : f = g ∘ e := funext fun ω => (h ω).symm
  rw [this, pr_equiv]

theorem pr_nonneg (f : Ω → Bool) : 0 ≤ pr f := by
  unfold pr
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact sum_nonneg fun ω _ => by split <;> norm_num

theorem pr_mono (f g : Ω → Bool) (h : ∀ ω, f ω = true → g ω = true) : pr f ≤ pr g := by
  unfold pr
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro ω _
  by_cases hf : f ω = true
  · simp [hf, h ω hf]
  · have hf' : f ω = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, ite_false]
    split <;> norm_num

theorem pr_le_one [Nonempty Ω] (f : Ω → Bool) : pr f ≤ 1 := by
  have h := pr_mono f (fun _ => true) (fun _ _ => rfl)
  have hc : (0 : ℚ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  refine h.trans (le_of_eq ?_)
  simp [pr, hc.ne']

/-- Hybrid bound: `|a - d| ≤ |a - b| + |b - c| + |c - d|` (written for the game-hop
chains below). -/
theorem abs_sub_le_three (a b c d : ℚ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  calc |a - d| = |(a - b) + (b - c) + (c - d)| := by congr 1; ring
    _ ≤ |(a - b) + (b - c)| + |c - d| := abs_add_le _ _
    _ ≤ |a - b| + |b - c| + |c - d| := by gcongr; exact abs_add_le _ _

end CryptoLean.PQ
