import CryptoLean.Curve.PrimeFieldBarrier
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The conductor discriminant identity bounds the size of a subgroup used in generic ECDLP. -/

set_option autoImplicit false

open scoped Polynomial

namespace CryptoLean.ConductorGap

open GenericDLog ECDLP PrimeFieldBarrier

/-- A divisor of the Frobenius conductor bounds the point count from below. -/
theorem conductor_divisor_sq_le_four_point_count {q pointCount f N : ℕ} {t D₀ : ℤ}
    (hD : t ^ 2 - 4 * (q : ℤ) = (f : ℤ) ^ 2 * D₀) (hnegative : t ^ 2 - 4 * (q : ℤ) < 0)
    (hdiv : N ∣ f) (hcount : (pointCount : ℤ) = (q : ℤ) + 1 - t) :
    (N : ℤ) ^ 2 * |D₀| ≤ 4 * (pointCount : ℤ) := by
  have hf : f ≠ 0 := by
    intro hz
    subst f
    rw [hD] at hnegative
    simp at hnegative
  have hNf : (N : ℤ) ≤ (f : ℤ) := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hf) hdiv
  have hsq : (N : ℤ) ^ 2 ≤ (f : ℤ) ^ 2 := pow_le_pow_left₀ (by positivity) hNf 2
  calc
    (N : ℤ) ^ 2 * |D₀| ≤ (f : ℤ) ^ 2 * |D₀| := mul_le_mul_of_nonneg_right hsq (abs_nonneg D₀)
    _ = |t ^ 2 - 4 * (q : ℤ)| := by rw [hD, abs_mul, abs_of_nonneg (sq_nonneg (f : ℤ))]
    _ = 4 * (pointCount : ℤ) - (t - 2) ^ 2 := by
      rw [abs_of_neg hnegative]
      linear_combination -4 * hcount
    _ ≤ _ := sub_le_self _ (sq_nonneg _)

/-- A point-count bound and a cofactor cap give a corresponding subgroup-order bound. -/
theorem sqrt_conductor_divisor_le_sqrt_order {G : Type*} [AddCommGroup G] {r H d : ℕ} {D₀ : ℤ}
    (P : G) (horder : addOrderOf P = r) (hH : 0 < H) (hcofactor : cofactor P ≤ H)
    (hcount : (d : ℤ) ^ 2 * |D₀| ≤ 4 * (Nat.card G : ℤ)) :
    Real.sqrt ((d : ℝ) ^ 2 * |(D₀ : ℝ)| / (4 * (H : ℝ))) ≤ Real.sqrt r := by
  have hsize : Nat.card G ≤ H * r := by
    rw [← cofactor_mul_order P, horder]
    exact Nat.mul_le_mul_right r hcofactor
  have hcountReal : (d : ℝ) ^ 2 * |(D₀ : ℝ)| ≤ 4 * (Nat.card G : ℝ) := by exact_mod_cast hcount
  have hsizeReal : (Nat.card G : ℝ) ≤ (H : ℝ) * (r : ℝ) := by exact_mod_cast hsize
  have hwork := hcountReal.trans (mul_le_mul_of_nonneg_left hsizeReal (by norm_num))
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ (mul_pos (by norm_num) (by exact_mod_cast hH))).mpr
  simpa only [mul_left_comm (r : ℝ) 4 (H : ℝ), mul_comm (r : ℝ) (H : ℝ)] using hwork

/-- Rescale the squared conductor-divisor bound and the subgroup order by the same factor. -/
theorem sqrt_conductor_divisor_le_sqrt_order_scaled {G : Type*} [AddCommGroup G] {r H d : ℕ} {D₀ : ℤ}
    (P : G) (horder : addOrderOf P = r) (hH : 0 < H) (hcofactor : cofactor P ≤ H)
    (hcount : (d : ℤ) ^ 2 * |D₀| ≤ 4 * (Nat.card G : ℤ)) (scale : ℝ) :
    Real.sqrt ((d : ℝ) ^ 2 * |(D₀ : ℝ)| / (4 * (H : ℝ) * scale)) ≤ Real.sqrt ((r : ℝ) / scale) := by
  rw [Real.sqrt_div (Nat.cast_nonneg r) scale, ← div_div, Real.sqrt_div (by positivity)]
  exact div_le_div_of_nonneg_right (sqrt_conductor_divisor_le_sqrt_order P horder hH hcofactor hcount)
    (Real.sqrt_nonneg scale)

/-- With a cofactor cap, the conductor divisor bounds every generic half-success budget. -/
theorem half_success_from_conductor_divisor {G : Type*} [AddCommGroup G] [DecidableEq G]
    {p r q f N H : ℕ} [Fact r.Prime] {t D₀ : ℤ}
    (hD : t ^ 2 - 4 * (p : ℤ) = (f : ℤ) ^ 2 * D₀) (hnegative : t ^ 2 - 4 * (p : ℤ) < 0)
    (hdiv : N ∣ f) (hcount : (Nat.card G : ℤ) = (p : ℤ) + 1 - t)
    (P : G) (horder : addOrderOf P = r) (hcofactor : cofactor P ≤ H)
    {View : ℕ → Type*} {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q)
    (hsuccess : (1 : ℝ) / 2 ≤ mixedPointSuccessProbability P weights observe samples strategy) :
    (N : ℤ) ^ 2 * |D₀| ≤ 4 * (H : ℤ) * (successNumerator q : ℤ) := by
  have hbound := conductor_divisor_sq_le_four_point_count hD hnegative hdiv hcount
  have hr := order_le_successNumerator_of_half (Fact.out : r.Prime).pos
    (mixedPointSuccessProbability_le P horder weights hnonneg hnorm observe samples strategy) hsuccess
  have hsize : Nat.card G ≤ H * successNumerator q := by
    rw [← cofactor_mul_order P, horder]
    exact Nat.mul_le_mul hcofactor hr
  refine hbound.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsize) (by norm_num)

/-- Every prime power in the valuation gap divides the Frobenius conductor. -/
theorem conductor_gap_power_dvd_frobenius {f₀ f₁ f N : ℕ} (hdiv : f₁ ∣ f) :
    N ^ (padicValNat N f₁ - padicValNat N f₀) ∣ f :=
  ((pow_dvd_pow N (Nat.sub_le _ _)).trans pow_padicValNat_dvd).trans hdiv

/-- A conductor divisor and cofactor cap bound the mean actual query count at half success. -/
theorem sqrt_conductor_divisor_le_of_half_success_with_expectedQueries {G : Type*}
    [AddCommGroup G] [DecidableEq G] {p r q f d H : ℕ} [Fact r.Prime] {t D₀ : ℤ}
    (hD : t ^ 2 - 4 * (p : ℤ) = (f : ℤ) ^ 2 * D₀) (hnegative : t ^ 2 - 4 * (p : ℤ) < 0)
    (hdiv : d ∣ f) (hcount : (Nat.card G : ℤ) = (p : ℤ) + 1 - t)
    (P : G) (horder : addOrderOf P = r) (hH : 0 < H) (hcofactor : cofactor P ≤ H)
    {View : ℕ → Type*} {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q)
    (hsuccess : (1 : ℝ) / 2 ≤ mixedPointSuccessProbability P weights observe samples strategy) :
    Real.sqrt ((d : ℝ) ^ 2 * |(D₀ : ℝ)| / (4 * (H : ℝ))) ≤
      8 * mixedPointExpectedQueries P weights observe samples strategy + 4 := by
  have hbound := conductor_divisor_sq_le_four_point_count hD hnegative hdiv hcount
  have hsubgroup := sqrt_conductor_divisor_le_sqrt_order P horder hH hcofactor hbound
  rw [mixedPointSuccessProbability_eq_scalar P horder] at hsuccess
  exact hsubgroup.trans (by
    rw [mixedPointExpectedQueries_eq_scalar P horder]
    exact sqrt_order_le_of_half_success_with_expectedQueries weights hnonneg hnorm observe samples strategy hsuccess)

/-- A conductor divisor bounds mean queries at half success with a certified exceptional set. -/
theorem sqrt_conductor_divisor_le_at_half_success_with_polynomial_exceptions {G : Type*}
    [AddCommGroup G] {p r q f d H : ℕ} [Fact r.Prime] {t D₀ : ℤ}
    (hD : t ^ 2 - 4 * (p : ℤ) = (f : ℤ) ^ 2 * D₀) (hnegative : t ^ 2 - 4 * (p : ℤ) < 0)
    (hdiv : d ∣ f) (hcount : (Nat.card G : ℤ) = (p : ℤ) + 1 - t)
    (P : G) (horder : addOrderOf P = r) (hH : 0 < H) (hcofactor : cofactor P ≤ H)
    {View : ℕ → Type*} {Seed ι : Type*} [Fintype Seed] [Fintype ι] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) (guess : Seed → ZMod r → ZMod r) (count : Seed → ZMod r → ℕ)
    (polynomials : Seed → ι → (ZMod r)[X]) (hnonzero : ∀ s i, polynomials s i ≠ 0)
    (hmatch : ∀ s x, (∀ i, (polynomials s i).eval x ≠ 0) →
      guess s x = scalarGuess (observe s) (samples s) (strategy s) x ∧
      scalarQueryCount (observe s) (samples s) (strategy s) x ≤ count s x)
    (hdegree : 4 * ∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ) ≤ (r : ℝ))
    (hsuccess : (1 : ℝ) / 2 ≤
      (∑ s, weights s * ((successfulSecrets (guess s)).card : ℝ)) / (r : ℝ)) :
    Real.sqrt ((d : ℝ) ^ 2 * |(D₀ : ℝ)| / (32 * (H : ℝ))) ≤
      8 * (∑ s, weights s * expectedQueries (count s)) + 2 := by
  have hbound := conductor_divisor_sq_le_four_point_count hD hnegative hdiv hcount
  have hsubgroup := sqrt_conductor_divisor_le_sqrt_order_scaled P horder hH hcofactor hbound 8
  have hmean := sqrt_order_div_eight_le_of_half_success_with_polynomial_exceptions weights hnonneg hnorm
    observe samples strategy guess count polynomials hnonzero hmatch hdegree hsuccess
  simpa only [show 4 * (H : ℝ) * 8 = 32 * (H : ℝ) by ring] using hsubgroup.trans hmean

/-- Solve the quadratic query bound for the budget. -/
theorem sqrt_gap_lower_bound_le_budget {N H m : ℕ} {D₀ : ℤ} (hH : 0 < H)
    (hwork : (N : ℤ) ^ 2 * |D₀| ≤ 4 * (H : ℤ) * (successNumerator m : ℤ)) :
    Real.sqrt ((N : ℝ) ^ 2 * |(D₀ : ℝ)| / (H : ℝ) - 7) ≤ 2 * (m : ℝ) + 5 := by
  have hreal : (N : ℝ) ^ 2 * |(D₀ : ℝ)| ≤ 4 * (H : ℝ) * (successNumerator m : ℝ) := by
    exact_mod_cast hwork
  have hquot : (N : ℝ) ^ 2 * |(D₀ : ℝ)| / (H : ℝ) ≤ 4 * (successNumerator m : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast hH)).mpr
    calc
      _ ≤ 4 * (H : ℝ) * (successNumerator m : ℝ) := hreal
      _ = _ := by ring
  have hnum : (successNumerator m : ℝ) = ((m : ℝ) + 3) * ((m : ℝ) + 2) + 2 := by
    simp [successNumerator]
  rw [hnum] at hquot
  exact (Real.sqrt_le_left (by positivity)).mpr (by nlinarith only [hquot])

end CryptoLean.ConductorGap
