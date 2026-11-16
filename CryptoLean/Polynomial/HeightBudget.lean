import CryptoLean.Polynomial.BalancedFiltration

/-! Necessary leaf-support tests for short ordinary-ideal certificates.
Unequal chart heights enter through an explicit weight lower bound.
No lattice-existence, root-extraction, saturation, or ECDLP success theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.HeightBudget

open CryptoLean.BalancedFiltration

/-- Lower chart height weakens the old coefficient filtration without losing
an exact integer bound. -/
theorem coefficient_height_lower (p H t d : ℕ) (c : ℤ)
    (hH : 1 ≤ H) (hp : H^2 ≤ p) (hc : c ≠ 0)
    (hd : (p : ℤ)^(t-d/2) ∣ c) :
    H^(2*t) ≤ c.natAbs * H^d := by
  have hdiv : p^(t-d/2) ∣ c.natAbs := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using
      Int.natAbs_dvd_natAbs.mpr hd
  have hcoeff : p^(t-d/2) ≤ c.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hdiv
  have he : 2*t ≤ (t-d/2)*2+d := by omega
  calc
    H^(2*t) ≤ H^((t-d/2)*2+d) := Nat.pow_le_pow_right (by omega) he
    _ = (H^2)^(t-d/2) * H^d := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ p^(t-d/2) * H^d := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp _)
    _ ≤ _ := Nat.mul_le_mul_right _ hcoeff

variable {σ : Type*}

def coefficientNorm (W : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ f.support, (f.coeff m).natAbs * W m

/-- An internal coordinate translation preserves ordinary chart membership. -/
theorem shifted_quadratic_mem [DecidableEq σ] (p : ℕ) (w : (σ →₀ ℕ) →+ ℕ) (u v : σ)
    (hu : w (Finsupp.single u 1) = 1) (hv : w (Finsupp.single v 1) = 1)
    (A B C τ : MvPolynomial σ ℤ) :
    A*(MvPolynomial.X u+τ*MvPolynomial.X v)^2 +
      B*(MvPolynomial.X u+τ*MvPolynomial.X v)*MvPolynomial.X v +
      C*MvPolynomial.X v^2 ∈ filtrationIdeal p w 1 := by
  have h := quadratic_chart_mem p w u v hu hv A (2*A*τ+B) (A*τ^2+B*τ+C)
  convert h using 1; ring

theorem filtered_coefficient_height_lower (p H t : ℕ)
    (hH : 1 ≤ H) (hp : H^2 ≤ p) (w : (σ →₀ ℕ) →+ ℕ)
    (f : MvPolynomial σ ℤ) (hf : Filtered p w t f)
    (m : σ →₀ ℕ) (hc : f.coeff m ≠ 0) :
    H^(2*t) ≤ (f.coeff m).natAbs * H^(w m) :=
  coefficient_height_lower p H t (w m) (f.coeff m) hH hp hc (hf m)

theorem coefficient_le_norm (W : (σ →₀ ℕ) → ℕ)
    (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) (hc : f.coeff m ≠ 0) :
    (f.coeff m).natAbs * W m ≤ coefficientNorm W f := by
  change (f.coeff m).natAbs * W m ≤
    ∑ n ∈ f.support, (f.coeff n).natAbs * W n
  exact Finset.single_le_sum
    (f := fun n ↦ (f.coeff n).natAbs * W n)
    (fun _ _ ↦ Nat.zero_le _) (MvPolynomial.mem_support_iff.mpr hc)

theorem leaf_term_norm_lower (p H t B : ℕ)
    (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (w : (σ →₀ ℕ) →+ ℕ) (leaf : (σ →₀ ℕ) → ℕ)
    (W : (σ →₀ ℕ) → ℕ)
    (hW : ∀ m, B^(leaf m) * H^(w m) ≤ W m)
    (f : MvPolynomial σ ℤ) (hf : Filtered p w t f)
    (m : σ →₀ ℕ) (hc : f.coeff m ≠ 0) (hl : 0 < leaf m) :
    B * H^(2*t) ≤ coefficientNorm W f := by
  have hleaf : B ≤ B^(leaf m) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hB (show 1 ≤ leaf m by omega)
  have hcoeff := filtered_coefficient_height_lower p H t hH hp w f hf m hc
  calc
    B * H^(2*t) ≤ B^(leaf m) * ((f.coeff m).natAbs * H^(w m)) :=
      Nat.mul_le_mul hleaf hcoeff
    _ = (f.coeff m).natAbs * (B^(leaf m) * H^(w m)) := by ring
    _ ≤ (f.coeff m).natAbs * W m := Nat.mul_le_mul_left _ (hW m)
    _ ≤ _ := coefficient_le_norm W f m hc

theorem short_leaf_coeff_zero (p H t B : ℕ)
    (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (w : (σ →₀ ℕ) →+ ℕ) (leaf : (σ →₀ ℕ) → ℕ)
    (W : (σ →₀ ℕ) → ℕ)
    (hW : ∀ m, B^(leaf m) * H^(w m) ≤ W m)
    (f : MvPolynomial σ ℤ) (hf : Filtered p w t f)
    (hshort : coefficientNorm W f < p^t) (hbudget : p^t ≤ B*H^(2*t))
    (m : σ →₀ ℕ) (hl : 0 < leaf m) : f.coeff m = 0 := by
  by_contra hc
  have hlow := leaf_term_norm_lower p H t B hH hp hB w leaf W hW f hf m hc hl
  exact (Nat.not_lt_of_ge (hbudget.trans hlow)) hshort

theorem span_power_short_leaf_coeff_zero [DecidableEq σ] (p H t B : ℕ)
    (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (w : (σ →₀ ℕ) →+ ℕ) (leaf : (σ →₀ ℕ) → ℕ)
    (W : (σ →₀ ℕ) → ℕ)
    (hW : ∀ m, B^(leaf m) * H^(w m) ≤ W m)
    (S : Set (MvPolynomial σ ℤ))
    (hS : ∀ g ∈ S, g ∈ filtrationIdeal p w 1)
    (f : MvPolynomial σ ℤ) (hf : f ∈ (Ideal.span S)^t)
    (hshort : coefficientNorm W f < p^t) (hbudget : p^t ≤ B*H^(2*t))
    (m : σ →₀ ℕ) (hl : 0 < leaf m) : f.coeff m = 0 := by
  have hJ : Ideal.span S ≤ filtrationIdeal p w 1 := Ideal.span_le.mpr hS
  have hpow := (pow_le_pow_left' hJ t).trans (ideal_pow_le p w t)
  exact short_leaf_coeff_zero p H t B hH hp hB w leaf W hW f (hpow hf)
    hshort hbudget m hl

/-- Per-slot bounds imply the minimum-height bound, retaining all grades. -/
theorem product_height_lower {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H : ℕ) (height degree : ι → ℕ)
    (hH : ∀ i ∈ s, H ≤ height i) :
    H^(∑ i ∈ s, degree i) ≤ ∏ i ∈ s, (height i)^(degree i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.prod_insert ha, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (hH a (Finset.mem_insert_self _ _)) _)
      (ih (fun i hi ↦ hH i (Finset.mem_insert_of_mem hi)))

theorem anisotropic_short_leaf_coeff_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (height : ι → ℕ) (degree : ι → (σ →₀ ℕ) → ℕ)
    (p H t B : ℕ) (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (hmin : ∀ i ∈ s, H ≤ height i)
    (w : (σ →₀ ℕ) →+ ℕ) (hw : ∀ m, w m = ∑ i ∈ s, degree i m)
    (leaf : (σ →₀ ℕ) → ℕ)
    (f : MvPolynomial σ ℤ) (hf : Filtered p w t f)
    (hshort : coefficientNorm (fun m ↦ B^(leaf m) *
      ∏ i ∈ s, (height i)^(degree i m)) f < p^t)
    (hbudget : p^t ≤ B*H^(2*t))
    (m : σ →₀ ℕ) (hl : 0 < leaf m) : f.coeff m = 0 := by
  apply short_leaf_coeff_zero p H t B hH hp hB w leaf
    (fun m ↦ B^(leaf m) * ∏ i ∈ s, (height i)^(degree i m)) ?_ f hf hshort hbudget m hl
  intro n
  apply Nat.mul_le_mul_left
  rw [hw]
  exact product_height_lower s H height (fun i ↦ degree i n) hmin

/-- Modulus-zero filtration records an ordinary positive-degree support gap. -/
theorem zero_filter_low_coeff (w : (σ →₀ ℕ) →+ ℕ)
    (f : MvPolynomial σ ℤ) (hf : Filtered 0 w 1 f)
    (m : σ →₀ ℕ) (hm : w m < 2) : f.coeff m = 0 := by
  have he : 1-w m/2 = 1 := by omega
  have h : (0 : ℤ) ∣ f.coeff m := by
    simpa only [he, pow_one, Nat.cast_zero] using hf m
  exact zero_dvd_iff.mp h

/-- A norm-short combination cannot retain a separated low-degree modulus part. -/
theorem short_modulus_part_zero (P : ℕ) (hP : 0 < P)
    (grade : (σ →₀ ℕ) → ℕ) (cut : ℕ)
    (W : (σ →₀ ℕ) → ℕ) (hW : ∀ m, 1 ≤ W m)
    (f a b : MvPolynomial σ ℤ)
    (ha : ∀ m, grade m < cut → a.coeff m = 0)
    (hb : ∀ m, b.coeff m ≠ 0 → grade m < cut)
    (hf : f=a+MvPolynomial.C (P : ℤ)*b)
    (hshort : coefficientNorm W f < P) : b=0 := by
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hc
  have hcoeff : f.coeff m = (P : ℤ)*b.coeff m := by
    rw [hf, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      MvPolynomial.coeff_C_mul, ha m (hb m hc), zero_add]
  have hnonzero : f.coeff m ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hP)) hc
  have hlarge : P ≤ (f.coeff m).natAbs := by
    rw [hcoeff, Int.natAbs_mul, Int.natAbs_natCast]
    calc
      P = P*1 := by simp
      _ ≤ _ := Nat.mul_le_mul_left P (Int.natAbs_pos.mpr hc)
  have hbound : P ≤ coefficientNorm W f := by
    calc
      P ≤ (f.coeff m).natAbs := hlarge
      _ = (f.coeff m).natAbs*1 := by simp
      _ ≤ (f.coeff m).natAbs*W m := Nat.mul_le_mul_left _ (hW m)
      _ ≤ _ := coefficient_le_norm W f m hnonzero
  exact (Nat.not_lt_of_ge hbound) hshort

theorem short_mem_original_ideal [DecidableEq σ]
    (I : Ideal (MvPolynomial σ ℤ)) (w : (σ →₀ ℕ) →+ ℕ)
    (hI : ∀ a ∈ I, Filtered 0 w 1 a)
    (P : ℕ) (hP : 0 < P) (W : (σ →₀ ℕ) → ℕ) (hW : ∀ m, 1 ≤ W m)
    (f a b : MvPolynomial σ ℤ) (ha : a ∈ I)
    (hb : ∀ m, b.coeff m ≠ 0 → w m < 2)
    (hf : f=a+MvPolynomial.C (P : ℤ)*b)
    (hshort : coefficientNorm W f < P) : f ∈ I := by
  have hb0 := short_modulus_part_zero P hP w 2 W hW f a b
    (fun m hm ↦ zero_filter_low_coeff w a (hI a ha) m hm) hb hf hshort
  simpa only [hf, hb0, mul_zero, add_zero] using ha

end CryptoLean.HeightBudget
