import CryptoLean.Polynomial.HeightBudget
import CryptoLean.Combinatorics.FieldRectangles
import Mathlib.Data.ZMod.Basic

/-! Exact coefficient windows and offset membership for norm-short rows.
No claim that every ECDLP selector has this residue form. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.ShortCoefficientWindows

open CryptoLean.HeightBudget CryptoLean.FieldRectangles
variable {σ : Type*}

theorem coefficient_bound_of_short (P n : ℕ)
    (W : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ)
    (hcut : P ≤ (n+1)*W m) (hshort : coefficientNorm W f < P) :
    (f.coeff m).natAbs ≤ n := by
  by_cases hc : f.coeff m=0
  · simp [hc]
  · by_contra hn
    have hlarge : n+1 ≤ (f.coeff m).natAbs := by omega
    have hbound := hcut.trans
      ((Nat.mul_le_mul_right (W m) hlarge).trans (coefficient_le_norm W f m hc))
    exact (Nat.not_lt_of_ge hbound) hshort

theorem integer_bounds_of_natAbs (n : ℕ) (z : ℤ) (hz : z.natAbs ≤ n) :
    -(n : ℤ) ≤ z ∧ z ≤ n := by
  have hu : z ≤ (z.natAbs : ℤ) := Int.le_natAbs
  have hl : -z ≤ ((-z).natAbs : ℤ) := Int.le_natAbs
  rw [Int.natAbs_neg] at hl
  have hc : (z.natAbs : ℤ) ≤ n := by exact_mod_cast hz
  constructor <;> omega

theorem short_has_nondivisible_coefficient (P : ℕ)
    (W : (σ →₀ ℕ) → ℕ) (hW : ∀ m, 1 ≤ W m)
    (f : MvPolynomial σ ℤ) (hf : f ≠ 0) (hshort : coefficientNorm W f < P) :
    ∃ m, ¬ (P : ℤ) ∣ f.coeff m := by
  by_contra! hdiv
  apply hf
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hc
  have hlarge : P ≤ (f.coeff m).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (Int.natCast_dvd.mp (hdiv m))
  have hbound : P ≤ coefficientNorm W f := by
    calc
      P ≤ (f.coeff m).natAbs := hlarge
      _ = (f.coeff m).natAbs*1 := by simp
      _ ≤ (f.coeff m).natAbs*W m := Nat.mul_le_mul_left _ (hW m)
      _ ≤ _ := coefficient_le_norm W f m hc
  exact (Nat.not_lt_of_ge hbound) hshort

theorem scalar_cast_ne_zero_of_short (p : ℕ) (scalar : ℤ)
    (W : (σ →₀ ℕ) → ℕ) (hW : ∀ m, 1 ≤ W m)
    (g F h : MvPolynomial σ ℤ) (hg : g ≠ 0)
    (hrow : g=MvPolynomial.C (p : ℤ)*h+MvPolynomial.C scalar*F)
    (hshort : coefficientNorm W g < p) : (scalar : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd scalar p).mp hzero
  obtain ⟨m,hm⟩ := short_has_nondivisible_coefficient p W hW g hg hshort
  apply hm
  rw [hrow, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  exact dvd_add (dvd_mul_right (p : ℤ) (h.coeff m))
    (dvd_mul_of_dvd_left hdiv (F.coeff m))

variable {K : Type*} [Field K] [DecidableEq K]

theorem offset_of_short_coefficients (P a b : ℕ)
    (W : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ ℤ)
    (m₁ m₂ : σ →₀ ℕ) (hshort : coefficientNorm W f < P)
    (hcut₁ : P ≤ (a+1)*W m₁) (hcut₂ : P ≤ (b+1)*W m₂)
    (scale center offset scalar : K) (hscale : scale ≠ 0) (hscalar : scalar ≠ 0)
    (hfirst : ((f.coeff m₁ : ℤ) : K)=scalar)
    (hsecond : ((f.coeff m₂ : ℤ) : K)=scale*scalar*(offset-center)) :
    offset ∈ rectangleImage scale center (intWindow K a) (intWindow K b) := by
  exact from_integer_coefficients scale center offset scalar hscale hscalar a b
    (f.coeff m₁) (f.coeff m₂)
    (integer_bounds_of_natAbs a _ (coefficient_bound_of_short P a W f m₁ hcut₁ hshort))
    (integer_bounds_of_natAbs b _ (coefficient_bound_of_short P b W f m₂ hcut₂ hshort))
    hfirst hsecond

end CryptoLean.ShortCoefficientWindows
