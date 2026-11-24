import CryptoLean.Polynomial.CurveParameterElimination

set_option autoImplicit false
noncomputable section
open CryptoLean.CurveParameterElimination

namespace DistinctGeneratorActual
variable {K : Type*} [Field K]

theorem translated_original_root (a b x y w U V X W τ σ : K)
    (hV : V ≠ 0) (hW : W ≠ 0)
    (h₁ : CryptoLean.Semaev.S3 a b x y ((U+τ*V)/V)=0)
    (h₂ : CryptoLean.Semaev.S3 a b ((U+τ*V)/V) w ((X+σ*W)/W)=0) :
    primitive a b x y w (U+τ*V) V (X+σ*W) W = 0 := by
  apply original_roots_primitive_zero
  · rw [first_clears_s3 a b x y _ _ hV,h₁,mul_zero]
  · rw [adjacent_clears_s3 a b w _ _ _ _ hV hW,h₂,mul_zero]

theorem actual_retained_branch (a b x y w Z V T W : K)
    (hA : firstSum x y Z V ≠ 0) :
    (first a b x y Z V=0 ∧ primitive a b x y w Z V T W=0) ↔
      (first a b x y Z V=0 ∧ adjacent a b w Z V T W=0) := by
  exact retained_equation_equiv (firstSum x y Z V) (adjacentSum w Z V T W*W)
    (first a b x y Z V) (adjacent a b w Z V T W) hA

theorem v_zero_nonzero (a b x y w Z T W : K) (hZ : Z ≠ 0)
    (h : (x-y)^2*W^2 ≠ (T-w*W)^2) : primitive a b x y w Z 0 T W ≠ 0 := by
  rw [primitive_v_zero]
  exact mul_ne_zero (pow_ne_zero 3 hZ) (sub_ne_zero.mpr h)

theorem w_zero_nonzero (a b x y w Z V T : K)
    (hA : Z+(x+y)*V ≠ 0) (hZ : Z-w*V ≠ 0) (hT : T ≠ 0) :
    primitive a b x y w Z V T 0 ≠ 0 := by
  rw [primitive_w_zero]
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hA) (pow_ne_zero 2 hZ))
    (pow_ne_zero 2 hT)

theorem universal_two_chart_cost {F σ : Type*} [Fintype F] [DecidableEq F]
    (p Q H₁ H₂ : ℕ) (hp : 0 < p) (hcardF : Fintype.card F=p)
    (hH : 1 ≤ H₁) (W : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ ℤ)
    (hf : f ≠ 0) (hweight : ∀ m ∈ f.support, H₁^3*H₂^2 ≤ W m)
    (hshort : CryptoLean.HeightBudget.coefficientNorm W f < p)
    (A : Fin Q → Finset (F×F)) (hcover : ∀ x, ∃ j, x ∈ A j)
    (hcard : ∀ j, (A j).card ≤ 9*(H₁^2*H₂^2)) : p < 9*Q := by
  have hN := nonzero_norm_min_weight (H₁^3*H₂^2) W f hf hweight
  have hK := profile_short_product H₁ H₂ _ p hH hN hshort
  have hc := cover_union_card Q (9*(H₁^2*H₂^2)) A hcover hcard
  rw [Fintype.card_prod,hcardF] at hc
  apply coverage_charge p Q (H₁^2*H₂^2) hp hK
  nlinarith

end DistinctGeneratorActual
