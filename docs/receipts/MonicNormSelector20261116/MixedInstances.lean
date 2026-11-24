import CryptoLean.Polynomial.DoublingNormResidues

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial CryptoLean.NormSaturatedInterpolation CryptoLean.DoublingNormResidues

namespace MonicNormMixedActual
variable {K : Type*} [Field K] [DecidableEq K] {W : WeierstrassCurve.Affine K}

theorem mixed_odd_subgroup_pool_residues {t b : ℕ}
    (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0) (htwo : (2:K) ≠ 0)
    (G H : W.Point) (q : ℕ) (hodd : q%2=1) (hG : q • G=0) (hH : q • H=0)
    (α β : Fin t × Fin b → ℕ) (hne : ∀ p, α p • G+β p • H ≠ 0) :
    ∃ x : Fin t × Fin b → K,
      (∀ p, (α p • G+β p • H).xRep= ![x p,1]) ∧
      ∀ choice : Fin t → Fin b, ∃ U : K[X], U.natDegree ≤ 2 ∧
        curveCubic W.a₄ W.a₆ ∣ U^2-∏ i : Fin t, (C (x (i,choice i))-X) := by
  apply every_colored_odd_tuple_passes_residue ha1 ha2 ha3 htwo
    (fun p ↦ α p • G+β p • H) hne q hodd
  intro p
  calc
    q • (α p • G+β p • H)=q • (α p • G)+q • (β p • H) := nsmul_add _ _ _
    _ = α p • (q • G)+β p • (q • H) := by
      congr 1
      all_goals rw [smul_smul,smul_smul,Nat.mul_comm]
    _ = 0 := by rw [hG,hH,nsmul_zero,nsmul_zero,zero_add]

end MonicNormMixedActual
