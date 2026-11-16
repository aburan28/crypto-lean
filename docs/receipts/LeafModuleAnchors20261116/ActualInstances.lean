import CryptoLean.Polynomial.LeafModuleAnchors

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.LeafModuleAnchors CryptoLean.RankTwoSourceAnchors

namespace LeafModuleActual
variable {K : Type*} [Field K]

theorem genuine_leaf_module_cover (a b τ σ : K)
    (A D : Polynomial (MvPolynomial (Fin 2) K)) (S : Finset K) (hD : D ≠ 0)
    (h₂ : (2 : K) ≠ 0)
    (hS : ∀ n m i, leafCode a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A D n m i ∈ S) :
    (a,b) ∈ curveCandidates S :=
  nonzero_module_curve_cover a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A D S hD h₂ hS

theorem arbitrary_order_same_code (a b τ σ : K) (A A' : Polynomial (MvPolynomial (Fin 2) K))
    (F : MvPolynomial (Fin 2) K) (n : ℕ) (m : Fin 2 →₀ ℕ) :
    leafCode a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A (C F*X^n) n m =
      leafCode a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A' (C F) 0 m := by
  have hl : ∀ i < n, (C F*X^n).coeff i=0 := by
    intro i hi
    simp [Nat.ne_of_lt hi]
  rw [leafCode_values _ _ _ _ _ _ _ _ _ _ hl,
    leafCode_values _ _ _ _ _ _ _ _ _ _ (by omega)]
  simp only [Polynomial.coeff_C_mul_X_pow,ite_true,Polynomial.coeff_C_zero]

theorem zero_second_code (a b τ σ : K) (A : Polynomial (MvPolynomial (Fin 2) K))
    (n : ℕ) (m : Fin 2 →₀ ℕ) :
    leafCode a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A 0 n m = ![0,0,0,0,0] := by
  rw [leafCode_values _ _ _ _ _ _ _ _ _ _ (by simp)]
  simp

/-- Choosing an arbitrary coefficient instead of the least one is unsound. -/
theorem nonleast_coefficient_control (a b x y : K) :
    (((moduleModel a b x y 1 1 0 0 0 1).coeff 2).coeff 1).coeff 1 = -2 := by
  have h := CryptoLean.RankTwoSourceAnchors.tu_anchors
    (C a) (C b) (C x) (C y) X (C 1) (C 1) 0 1 (C 0) (C 0)
  simp only [moduleModel,h.2.1]
  norm_num

theorem bounded_integer_module_cover (p T : ℕ) [Fact p.Prime]
    (a b τ σ : ZMod p) (A D : Polynomial (MvPolynomial (Fin 2) (ZMod p)))
    (r : ℕ → (Fin 2 →₀ ℕ) → Fin 5 → ℤ) (hD : D ≠ 0) (h₂ : (2 : ZMod p) ≠ 0)
    (hr : ∀ n m i, (r n m i : ZMod p)=
      leafCode a b τ σ (MvPolynomial.X 0) (MvPolynomial.X 1) A D n m i)
    (hT : ∀ n m i, (r n m i).natAbs ≤ T) :
    (a,b) ∈ curveCandidates (CryptoLean.FieldRectangles.intWindow (ZMod p) T) := by
  apply genuine_leaf_module_cover a b τ σ A D _ hD h₂
  intro n m i
  rw [← hr n m i]
  exact CryptoLean.FieldRectangles.mem_intWindow_of_bounds T (r n m i)
    (CryptoLean.ShortCoefficientWindows.integer_bounds_of_natAbs T (r n m i) (hT n m i))

end LeafModuleActual
