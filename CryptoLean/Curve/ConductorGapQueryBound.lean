import CryptoLean.Curve.SubgroupDLog

/-! The conductor discriminant identity bounds the size of a subgroup used in generic ECDLP. -/

set_option autoImplicit false

namespace CryptoLean.ConductorGap

open GenericDLog ECDLP

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
