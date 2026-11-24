import CryptoLean.Polynomial.CubicAdicLifting

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial CryptoLean.CubicAdicLifting CryptoLean.NormSaturatedInterpolation

namespace CubicAdicMixedActual
variable {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve.Affine K}

theorem mixed_pool_all_precisions {t b : ℕ}
    (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0) (htwo : (2:K) ≠ 0)
    (G H : W.Point) (q : ℕ) (hodd : q%2=1) (hG : q • G=0) (hH : q • H=0)
    (α β : Fin t × Fin b → ℕ) (hne : ∀ p, α p • G+β p • H ≠ 0) :
    ∃ x : Fin t × Fin b → K, (∀ p, (α p • G+β p • H).xRep= ![x p,1]) ∧
      ∀ choice : Fin t → Fin b, ∀ k : ℕ, 0 < k →
        ∃ U : K[X], U.natDegree < 3*k ∧
          (curveCubic W.a₄ W.a₆)^k ∣ U^2-∏ i : Fin t, (C (x (i,choice i))-X) := by
  apply every_colored_odd_tuple_all_powers ha1 ha2 ha3 htwo
    (fun p ↦ α p • G+β p • H) hne q hodd
  intro p
  calc
    q • (α p • G+β p • H)=q • (α p • G)+q • (β p • H) := nsmul_add _ _ _
    _ = α p • (q • G)+β p • (q • H) := by
      congr 1
      all_goals rw [smul_smul,smul_smul,Nat.mul_comm]
    _ = 0 := by rw [hG,hH,nsmul_zero,nsmul_zero,zero_add]

theorem mixed_pool_low_precision_cap {t b : ℕ}
    (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0) (htwo : (2:K) ≠ 0)
    (G H : W.Point) (q : ℕ) (hodd : q%2=1) (hG : q • G=0) (hH : q • H=0)
    (α β : Fin t × Fin b → ℕ) (hne : ∀ p, α p • G+β p • H ≠ 0)
    (k : ℕ) (hk : 0 < k) (hlow : 6*k ≤ t+2) :
    ∃ x : Fin t × Fin b → K, (∀ p, (α p • G+β p • H).xRep= ![x p,1]) ∧
      ∀ choice : Fin t → Fin b, ∃ U : K[X], U.natDegree ≤ t/2 ∧
        (curveCubic W.a₄ W.a₆)^k ∣ U^2-∏ i : Fin t, (C (x (i,choice i))-X) := by
  obtain ⟨x,hx,hroot⟩ := mixed_pool_all_precisions ha1 ha2 ha3 htwo G H q hodd hG hH α β hne
  refine ⟨x,hx,?_⟩
  intro choice
  obtain ⟨U,hdeg,hU⟩ := hroot choice k hk
  exact ⟨U,by omega,hU⟩

end CubicAdicMixedActual
