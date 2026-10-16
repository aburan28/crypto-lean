/-!
# State-count bounds for the N83 root tables

The N83 capacity proofs in `aburan28/crypto` (`research/n83_*`) each defined
their own `stateBound`. They use two different models:

* `pairStates k = 83·(k(k−1)/2) + 42k`: unordered pairs of distinct factor-base
  columns, 83 Frobenius positions each, plus 42 per single column. Written as
  `83 * (k * (k - 1) / 2) + 42 * k` in most files and as
  `83 * k * (k - 1) / 2 + 42 * k` in `n83_root4_highk_results_20261015`.
  `pairStates_eq_alt` proves the two spellings equal for every `k`.
* `squareStates k = 83·k²`: the looser ordered-pairs model of
  `n83_indexed5_tier1_results_20261013/Capacity16G.lean`.
  `pairStates_le_squareStates` proves it is an upper bound.

`requestedEntries` is the table request at 75% load: `⌈4s/3⌉` written as
`(4s + 2) / 3`.
-/

namespace CryptoLeanCore.N83

def pairStates (k : Nat) : Nat := 83 * (k * (k - 1) / 2) + 42 * k

def squareStates (k : Nat) : Nat := 83 * (k * k)

def requestedEntries (states : Nat) : Nat := (4 * states + 2) / 3

theorem two_dvd_mul_pred (k : Nat) : 2 ∣ k * (k - 1) := by
  induction k with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    simp only [Nat.add_sub_cancel]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h) (Nat.dvd_mul_left n (n + 1))
    · have : 2 ∣ n + 1 := by omega
      exact Nat.dvd_trans this (Nat.dvd_mul_right (n + 1) n)

/-- The two spellings of `pairStates` in the source files agree for every `k`. -/
theorem pairStates_eq_alt (k : Nat) : pairStates k = 83 * k * (k - 1) / 2 + 42 * k := by
  unfold pairStates
  obtain ⟨m, hm⟩ := two_dvd_mul_pred k
  have h1 : k * (k - 1) / 2 = m := by omega
  have h2 : 83 * k * (k - 1) = 2 * (83 * m) := by
    rw [Nat.mul_assoc, hm]; rw [Nat.mul_left_comm]
  have h3 : 83 * k * (k - 1) / 2 = 83 * m := by omega
  rw [h1, h3]

theorem pairStates_le_squareStates (k : Nat) : pairStates k ≤ squareStates k := by
  unfold pairStates squareStates
  obtain ⟨m, hm⟩ := two_dvd_mul_pred k
  have h1 : k * (k - 1) / 2 = m := by omega
  rw [h1]
  rcases k with _ | k
  · simp at hm; omega
  · have hk : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by rw [Nat.mul_succ]
    simp only [Nat.add_sub_cancel] at hm
    omega

theorem pairStates_mono {a b : Nat} (h : a ≤ b) : pairStates a ≤ pairStates b := by
  unfold pairStates
  have : a * (a - 1) ≤ b * (b - 1) := Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)
  have : a * (a - 1) / 2 ≤ b * (b - 1) / 2 := Nat.div_le_div_right this
  omega

theorem requestedEntries_mono {a b : Nat} (h : a ≤ b) :
    requestedEntries a ≤ requestedEntries b := by
  unfold requestedEntries; exact Nat.div_le_div_right (by omega)

end CryptoLeanCore.N83
