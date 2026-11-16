import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section

#check MvPolynomial.coeff_mul
#check MvPolynomial.coeff_add
#check Finset.mem_antidiagonal
#check Finset.dvd_sum
#check pow_dvd_pow
#check Ideal.mul_le
#check Ideal.span_le
#check pow_succ
#check Int.natAbs_dvd_natAbs
#check Int.natAbs_pos
#check Int.natAbs_pow
#check Nat.pow_le_pow_right
#check Nat.pow_le_pow_left
#check MvPolynomial.X_pow_eq_monomial
#check MvPolynomial.monomial_mul_monomial

example (t u d e : ℕ) : t+u-(d+e)/2 ≤ (t-d/2)+(u-e/2) := by omega

example {σ : Type*} [DecidableEq σ] (f g : MvPolynomial σ ℤ)
    (m : σ →₀ ℕ) (a : ℤ)
    (h : ∀ n ∈ Finset.antidiagonal m, a ∣ f.coeff n.1 * g.coeff n.2) :
    a ∣ (f*g).coeff m := by
  rw [MvPolynomial.coeff_mul]
  exact Finset.dvd_sum h

example (p : ℤ) (a b : ℕ) (h : a ≤ b) : p^a ∣ p^b := pow_dvd_pow p h
