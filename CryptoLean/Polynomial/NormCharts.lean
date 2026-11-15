import Mathlib.FieldTheory.Separable

/-! Generic polynomial laws for removing redundant norm-chart witnesses. -/
namespace CryptoLean.Polynomial
open _root_.Polynomial

/-- A squarefree divisor of a squarefree quadratic norm is coprime to its
second norm coordinate. No assumption on the curve polynomial is required. -/
theorem isRelPrime_of_squarefree_norm {K : Type*} [Field K]
    {A B f U N : K[X]} (hU : Squarefree U) (hN : Squarefree N)
    (hdiv : U ∣ N) (hnorm : A^2-f*B^2=N) : IsRelPrime U B := by
  intro D hDU hDB
  have hD : Squarefree D := Squarefree.squarefree_of_dvd hDU hU
  have hDN : D ∣ N := hDU.trans hdiv
  have hDB2 : D ∣ B^2 := dvd_pow hDB (by decide : 2 ≠ 0)
  have hDA2 : D ∣ A^2 := by
    have h := dvd_add hDN (dvd_mul_of_dvd_right hDB2 f)
    rwa [← hnorm, sub_add_cancel] at h
  have hDA : D ∣ A := (hD.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hDA2
  apply hN D
  rw [← hnorm]
  apply dvd_sub
  · simpa only [pow_two] using pow_dvd_pow_of_dvd hDA 2
  · have hDBsq : D*D ∣ B^2 := by
      simpa only [pow_two] using pow_dvd_pow_of_dvd hDB 2
    exact dvd_mul_of_dvd_right hDBsq f

/-- Nonzero Kummer membership and target separation discharge separability
and both coprimality predicates used by the norm witness blocks. -/
theorem kummer_norm_charts {K : Type*} [Field K]
    {A B f U : K[X]} {c r : K} {d : ℕ}
    (hd : (d : K) ≠ 0) (hc : c ≠ 0) (hm : U ∣ X^d-C c)
    (hr : U.eval r ≠ 0) (hnorm : A^2-f*B^2=(X-C r)*U) :
    U.Separable ∧ IsCoprime U (derivative U) ∧ IsCoprime U B := by
  have hu := (separable_X_pow_sub_C c hd hc).of_dvd hm
  have hcop : IsCoprime (X-C r) U := by
    apply Or.resolve_left (EuclideanDomain.dvd_or_coprime (X-C r) U
      (irreducible_of_degree_eq_one (degree_X_sub_C r)))
    simpa only [dvd_iff_isRoot, IsRoot] using hr
  have hn := (separable_X_sub_C.mul hu hcop).squarefree
  exact ⟨hu, hu, isRelPrime_iff_isCoprime.mp
    (isRelPrime_of_squarefree_norm hu.squarefree hn (dvd_mul_left U _) hnorm)⟩

end CryptoLean.Polynomial
