import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Finite.Basic

/-! Semantic completeness of an explicit root certificate. The consumer checks
that its claimed distinct roots multiply to a monic gcd. These statements do
not verify a native parser, polynomial implementation, or prime admission. -/
set_option autoImplicit false
namespace CryptoLean.Polynomial
open _root_.Polynomial

/-- If `g` vanishes everywhere, the normalized gcd with `g` certifies all
field roots of `f`, including the case of repeated roots of `f`. -/
theorem complete_roots_of_gcd {K : Type*} [Field K] [DecidableEq K]
    (f g : K[X]) (s : Finset K) (hg : ∀ x : K, g.IsRoot x)
    (hcert : normalize (EuclideanDomain.gcd f g) = ∏ a ∈ s, (X-C a)) (x : K) :
    f.IsRoot x ↔ x ∈ s := by
  have hprod : (∏ a ∈ s, (X-C a) : K[X]) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun a _ => X_sub_C_ne_zero a)
  have hn : EuclideanDomain.gcd f g ≠ 0 := by
    intro hz
    apply hprod
    rw [← hcert, hz]
    simp
  have hroots : (EuclideanDomain.gcd f g).roots = s.val := by
    rw [← roots_normalize (p := EuclideanDomain.gcd f g), hcert, roots_prod_X_sub_C]
  calc
    f.IsRoot x ↔ (EuclideanDomain.gcd f g).IsRoot x := by
      rw [isRoot_gcd_iff_isRoot_left_right]
      simp only [hg x, and_true]
    _ ↔ x ∈ s := by
      rw [← mem_roots hn, hroots]
      simp

/-- Over a finite field, `X^|K|-X` supplies the universally vanishing
polynomial. The certificate lists exactly the distinct roots of `f`. -/
theorem complete_roots_of_frobenius_gcd {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (f : K[X]) (s : Finset K)
    (hcert : normalize (EuclideanDomain.gcd f (X^(Fintype.card K)-X)) =
      ∏ a ∈ s, (X-C a)) (x : K) : f.IsRoot x ↔ x ∈ s := by
  apply complete_roots_of_gcd f (X^(Fintype.card K)-X) s _ hcert x
  intro y
  simp [IsRoot, FiniteField.pow_card]

end CryptoLean.Polynomial
