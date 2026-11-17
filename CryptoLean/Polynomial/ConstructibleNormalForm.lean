import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic

/-! A generic actual-degree normal-form argument over existing polynomial and
submodule structures. This file does not construct a tower or assert its NF
contracts; those remain instance obligations. -/
namespace CryptoLean.Polynomial
open MvPolynomial

variable {σ k : Type*} [Field k]

theorem normalForm_constructible_bound
    (W : ℕ → Submodule k (MvPolynomial σ k))
    (hmono : Monotone W)
    (hmul : ∀ {i} {f g : MvPolynomial σ k}, f ∈ W i →
      f.totalDegree + g.totalDegree ≤ i → f * g ∈ W i)
    (T : ℕ)
    (nf : MvPolynomial σ k →ₗ[k] MvPolynomial σ k)
    (hdeg : ∀ p, (nf p).totalDegree < T)
    (hone : (1 : MvPolynomial σ k) - nf 1 ∈ W T)
    (hact : ∀ p i, nf p * X i - nf (nf p * X i) ∈ W T)
    (hcompat : ∀ p i, nf (nf p * X i) = nf (p * X i))
    (f : MvPolynomial σ k) : f - nf f ∈ W (max T f.totalDegree) := by
  classical
  have hmonomial : ∀ s a, monomial s a - nf (monomial s a) ∈
      W (max T (monomial s a).totalDegree) := by
    apply induction_on_monomial (motive := fun p => p - nf p ∈ W (max T p.totalDegree))
    · intro a
      have h := (W T).smul_mem a hone
      rw [totalDegree_C, max_zero]
      simpa only [C_eq_smul_one, map_smul, smul_sub] using h
    · intro p i ih
      by_cases hp : p = 0
      · simp [hp]
      have hd := totalDegree_sub p (nf p)
      have hn := hdeg p
      have hb : (p - nf p).totalDegree + (X i : MvPolynomial σ k).totalDegree ≤
          max T (p * X i).totalDegree := by
        rw [totalDegree_X, totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
      have hinc : max T p.totalDegree ≤ max T (p * X i).totalDegree := by
        rw [totalDegree_mul_of_isDomain hp (X_ne_zero i), totalDegree_X]
        omega
      have hleft := hmul (hmono hinc ih) hb
      have hright := hmono (le_max_left T (p * X i).totalDegree) (hact p i)
      rw [hcompat p i] at hright
      have hsum := (W (max T (p * X i).totalDegree)).add_mem hleft hright
      simpa only [sub_mul, sub_add_sub_cancel] using hsum
  have hsum : (∑ s ∈ f.support,
      (monomial s (f.coeff s) - nf (monomial s (f.coeff s)))) ∈
      W (max T f.totalDegree) := by
    apply Submodule.sum_mem
    intro s hs
    have hsdeg : (monomial s (f.coeff s) : MvPolynomial σ k).totalDegree ≤
        f.totalDegree := by
      exact (totalDegree_monomial_le _ _).trans (le_totalDegree hs)
    exact hmono (max_le_max_left T hsdeg) (hmonomial s (f.coeff s))
  simpa only [Finset.sum_sub_distrib, ← map_sum, ← MvPolynomial.as_sum] using hsum

#print axioms normalForm_constructible_bound
end CryptoLean.Polynomial
