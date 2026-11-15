import CryptoLean.Curve.Conductor
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace CryptoLean

/-- A reciprocal root and a coefficient relation expose two divisible terms.
This is the sole opening of the inherited quadratic norm in this module. -/
theorem quadraticNorm_reciprocal_factorization (t u a b ell : ℤ) :
    quadraticNorm t u a b =
      a^2 * (1-t*ell+u*ell^2) + (b+ell*a) * (u*b+(t-u*ell)*a) := by
  unfold quadraticNorm
  ring

/-- Generic quadratic-norm divisibility; no primality or curve hypothesis. -/
theorem quadraticNorm_dvd_of_reciprocal_root {n t u a b ell : ℤ}
    (hroot : n ∣ 1-t*ell+u*ell^2) (hline : n ∣ b+ell*a) :
    n ∣ quadraticNorm t u a b := by
  rw [quadraticNorm_reciprocal_factorization t u a b ell]
  exact dvd_add (Int.dvd_mul_of_dvd_right hroot) (Int.dvd_mul_of_dvd_left hline)

theorem eisenstein_norm_doubled (a b : ℤ) :
    2 * quadraticNorm (-1) 1 a b = (a-b)^2 + a^2 + b^2 := by
  rw [quadraticNorm_reciprocal_factorization (-1) 1 a b 0]
  ring

theorem eisenstein_norm_pos {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0) :
    0 < quadraticNorm (-1) 1 a b := by
  have h := eisenstein_norm_doubled a b
  rcases hne with ha | hb
  · have hpos := sq_pos_of_ne_zero ha
    nlinarith [sq_nonneg (a-b), sq_nonneg b]
  · have hpos := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg (a-b), sq_nonneg a]

/-- The positive-multiple bound is inherited from Int.le_of_dvd. -/
theorem eisenstein_norm_lower_bound {n a b ell : ℤ}
    (hroot : n ∣ ell^2+ell+1) (hline : n ∣ b+ell*a)
    (hne : a ≠ 0 ∨ b ≠ 0) : n ≤ quadraticNorm (-1) 1 a b := by
  have hr : n ∣ 1-(-1)*ell+1*ell^2 := by
    convert hroot using 1; ring
  exact Int.le_of_dvd (eisenstein_norm_pos hne)
    (quadraticNorm_dvd_of_reciprocal_root hr hline)

theorem eisenstein_norm_rotate (a b : ℤ) :
    quadraticNorm (-1) 1 (-b) (a-b) = quadraticNorm (-1) 1 a b := by
  rw [quadraticNorm_reciprocal_factorization (-1) 1 (-b) (a-b) 0,
      quadraticNorm_reciprocal_factorization (-1) 1 a b 0]
  ring

/-- In the open opposite-sign sector, both coefficient squares are below the norm. -/
theorem eisenstein_sector_bounds {a b n : ℤ} (ha : 0 < a) (hb : b < 0)
    (hnorm : quadraticNorm (-1) 1 a b = n) : a^2 < n ∧ b^2 < n := by
  rw [quadraticNorm_reciprocal_factorization (-1) 1 a b 0] at hnorm
  have hab := mul_neg_of_pos_of_neg ha hb
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

end CryptoLean
