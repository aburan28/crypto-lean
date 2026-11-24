import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# The endomorphisms `ι` and `π` of `E₀ : y² = x³ + x`, and `πι = -ιπ`

On `E₀ : y² = x³ + x` over a field `K` of characteristic `p` containing `√-1` (written
`s`, `s² = -1`; for SQIsign `K = F_{p²}`), the maps

* `ι (x, y) = (-x, s y)` (the automorphism of order 4), and
* `π (x, y) = (x^p, y^p)` (the `p`-power Frobenius)

send affine points of `E₀` to affine points of `E₀`. When `p ≡ 3 (mod 4)`, `s^p = -s`, so
`π ∘ ι = neg ∘ ι ∘ π`, where `neg (x, y) = (x, -y)` is the negation map of the curve.
`ι ∘ ι = neg`. In `End(E₀) ≅ O₀` these are the relations `i² = -1` and `ji = -ij` of
`B_{p,∞}` (`relations` in `MaximalOrderO0.lean`), with `i ↦ ι`, `j ↦ π`. This file proves
them on affine coordinates. Identifying these maps with elements of the endomorphism ring
(the group-law statement, and `π² = [-p]`) is **not** formalized here.
-/

set_option autoImplicit false

namespace CryptoLean.Deuring

variable {K : Type*} [Field K]

/-- The affine equation of `E₀`. -/
def onE0 (P : K × K) : Prop := P.2 ^ 2 = P.1 ^ 3 + P.1

def iota (s : K) (P : K × K) : K × K := (-P.1, s * P.2)
def frob (p : ℕ) (P : K × K) : K × K := (P.1 ^ p, P.2 ^ p)
def negE (P : K × K) : K × K := (P.1, -P.2)

theorem iota_onE0 {s : K} (hs : s ^ 2 = -1) {P : K × K} (hP : onE0 P) : onE0 (iota s P) := by
  unfold onE0 iota at *
  simp only
  calc (s * P.2) ^ 2 = s ^ 2 * P.2 ^ 2 := by ring
    _ = -(P.1 ^ 3 + P.1) := by rw [hs, hP]; ring
    _ = (-P.1) ^ 3 + -P.1 := by ring

theorem iota_iota {s : K} (hs : s ^ 2 = -1) (P : K × K) : iota s (iota s P) = negE P := by
  unfold iota negE
  ext
  · simp
  · simp only
    calc s * (s * P.2) = s ^ 2 * P.2 := by ring
      _ = -P.2 := by rw [hs]; ring

theorem frob_onE0 (p : ℕ) [Fact p.Prime] [CharP K p] {P : K × K} (hP : onE0 P) :
    onE0 (frob p P) := by
  unfold onE0 frob at *
  simp only
  rw [← pow_mul, mul_comm, pow_mul, hP, add_pow_char, ← pow_mul, mul_comm, pow_mul]

/-- `s^p = -s` when `s² = -1` and `p ≡ 3 (mod 4)`. -/
theorem sqrt_neg_one_pow {s : K} (hs : s ^ 2 = -1) (m : ℕ) : s ^ (4 * m + 3) = -s := by
  have h4 : s ^ 4 = 1 := by
    calc s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hs]; ring
  calc s ^ (4 * m + 3) = (s ^ 4) ^ m * (s ^ 2 * s) := by ring
    _ = -s := by rw [h4, hs]; ring

/-- **`π ι = -ι π`** on `E₀` for `p = 4m + 3` (the relation `ji = -ij`). -/
theorem frob_iota (m : ℕ) [Fact (4 * m + 3).Prime] [CharP K (4 * m + 3)] {s : K}
    (hs : s ^ 2 = -1) (P : K × K) :
    frob (4 * m + 3) (iota s P) = negE (iota s (frob (4 * m + 3) P)) := by
  unfold frob iota negE
  have hodd : Odd (4 * m + 3) := ⟨2 * m + 1, by ring⟩
  ext
  · simp only
    rw [hodd.neg_pow]
  · simp only
    rw [mul_pow, sqrt_neg_one_pow hs m]
    ring

end CryptoLean.Deuring
