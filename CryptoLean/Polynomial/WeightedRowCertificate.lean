import CryptoLean.Polynomial.RankOneSelector

/-! Integer-value vanishing from a row witness and an exact weighted norm.
The monomial/root interpretation is supplied by the consumer. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.WeightedRowCertificate
open CryptoLean.RankOneSelector
variable {ι : Type*} [Fintype ι]

def rowValue (row values : ι → ℤ) : ℤ := ∑ i, row i*values i

theorem weighted_value_bound (weight : ι → ℕ) (row values : ι → ℤ)
    (hvalues : ∀ i, (values i).natAbs ≤ weight i) :
    (rowValue row values).natAbs ≤ rowNorm weight row := by
  calc
    _ ≤ ∑ i, (row i*values i).natAbs := Int.natAbs_sum_le _ _
    _ = ∑ i, (row i).natAbs*(values i).natAbs := by
      apply Finset.sum_congr rfl
      intro i _
      exact Int.natAbs_mul _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ Nat.mul_le_mul_left _ (hvalues i))

theorem row_value_divisible (p : ℕ) (scalar : ℤ) (row base F values : ι → ℤ)
    (hrow : ∀ i, row i=(p : ℤ)*base i+scalar*F i)
    (hF : (p : ℤ) ∣ rowValue F values) : (p : ℤ) ∣ rowValue row values := by
  have he : rowValue row values =
      (p : ℤ)*rowValue base values+scalar*rowValue F values := by
    simp only [rowValue,hrow,add_mul,mul_assoc,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  exact dvd_add (dvd_mul_right (p : ℤ) (rowValue base values))
    (dvd_mul_of_dvd_right hF scalar)

theorem short_row_value_zero (p : ℕ) (weight : ι → ℕ) (row values : ι → ℤ)
    (hvalues : ∀ i, (values i).natAbs ≤ weight i)
    (hshort : rowNorm weight row < p) (hdiv : (p : ℤ) ∣ rowValue row values) :
    rowValue row values=0 := by
  by_contra hne
  have hlarge : p ≤ (rowValue row values).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp hdiv)
  exact (Nat.not_lt_of_ge (hlarge.trans (weighted_value_bound weight row values hvalues))) hshort

end CryptoLean.WeightedRowCertificate
