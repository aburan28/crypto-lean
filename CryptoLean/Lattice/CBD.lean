import Mathlib.Tactic.DeriveFintype

/-!
# The centred binomial distribution of ML-KEM

FIPS 203 (August 2024) §4.2.2, Algorithm 8 (`SamplePolyCBD_η`): a coefficient is
`x - y` with `x = Σ_{j<η} b_{2iη+j}` and `y = Σ_{j<η} b_{2iη+η+j}`, the bits `b` uniform.
Here a draw of `2η` bits is a number `w < 4^η`: `x` is the popcount of its low `η` bits,
`y` of its high `η` bits. Exact moments for the two `η` ML-KEM uses (`η ∈ {2, 3}`), by
kernel `decide` over all `4^η` equally likely bit strings:

* support `[-η, η]`, mean 0 (`Σ v = 0`), variance `η/2` (`2·Σ v² = η·4^η`);
* the probability table, as counts out of `4^η` (`cbd_counts_2`, `cbd_counts_3`).

These are the numbers the ML-KEM decryption-failure computation starts from.
-/

set_option autoImplicit false

namespace CryptoLean.Lattice

/-- Number of one bits among the lowest `k` bits of `w`. -/
def popLow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, w => w % 2 + popLow k (w / 2)

/-- The CBD_η value of the bit string `w < 4^η`. -/
def cbdValue (η w : ℕ) : ℤ :=
  (popLow η (w % 2 ^ η) : ℤ) - (popLow η (w / 2 ^ η) : ℤ)

/-- All `4^η` equally likely values. -/
def cbdValues (η : ℕ) : List ℤ :=
  (List.range (4 ^ η)).map (cbdValue η)

theorem cbd_support (η : ℕ) (hη : η ∈ [2, 3]) : ∀ v ∈ cbdValues η, -(η : ℤ) ≤ v ∧ v ≤ η := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hη
  rcases hη with rfl | rfl <;> decide +kernel

theorem cbd_mean_zero (η : ℕ) (hη : η ∈ [2, 3]) : (cbdValues η).sum = 0 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hη
  rcases hη with rfl | rfl <;> decide +kernel

/-- Variance `η/2`: `2 · Σ v² = η · 4^η`. -/
theorem cbd_variance (η : ℕ) (hη : η ∈ [2, 3]) :
    2 * ((cbdValues η).map (· ^ 2)).sum = (η : ℤ) * 4 ^ η := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hη
  rcases hη with rfl | rfl <;> decide +kernel

/-- CBD₂: `P(v) = (1, 4, 6, 4, 1)/16` on `v = -2..2`. -/
theorem cbd_counts_2 :
    ([-2, -1, 0, 1, 2] : List ℤ).map (fun v => (cbdValues 2).count v) = [1, 4, 6, 4, 1] := by
  decide +kernel

/-- CBD₃: `P(v) = (1, 6, 15, 20, 15, 6, 1)/64` on `v = -3..3`. -/
theorem cbd_counts_3 :
    ([-3, -2, -1, 0, 1, 2, 3] : List ℤ).map (fun v => (cbdValues 3).count v)
      = [1, 6, 15, 20, 15, 6, 1] := by
  decide +kernel

end CryptoLean.Lattice
