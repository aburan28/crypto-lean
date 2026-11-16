import CryptoLean.Polynomial.ResidualLeafRank

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial CryptoLean.ResidualLeafRank

namespace ResidualRankActual
variable {K : Type*} [Field K]

theorem original_source_reconstruction {S : Type*} [CommRing S] (f : Leaf K →+* S)
    (a b τ σ : K) (U V T W : S) :
    CryptoLean.ProjectiveSubresultant.residual (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
      (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1)) (f (MvPolynomial.X 2))
      (U+f (MvPolynomial.C τ)*V) V (T+f (MvPolynomial.C σ)*W) W =
      f (sourceBlocks a b τ σ 0)*U*T^2+f (sourceBlocks a b τ σ 1)*U*T*W+
      f (sourceBlocks a b τ σ 2)*U*W^2+f (sourceBlocks a b τ σ 3)*V*T^2+
      f (sourceBlocks a b τ σ 4)*V*T*W+f (sourceBlocks a b τ σ 5)*V*W^2 := by
  have h := source_homogeneous_blocks (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
    (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1)) (f (MvPolynomial.X 2))
    (f (MvPolynomial.C τ)) (f (MvPolynomial.C σ)) U V T W
  simp only [← block_map f] at h
  simpa only [sourceBlocks] using h

theorem repeated_blocks_keep_six_tags (A : Finset (Fin 3 →₀ ℕ)) :
    (honestSupport A (fun _ : Fin 6 ↦ (1 : Leaf K))).card=6*A.card := by
  classical
  have h : rowSupport A (1 : Leaf K)=A := by
    ext m
    simp [rowSupport,MvPolynomial.support_monomial]
  simp [honestSupport,h,Finset.card_sigma,Nat.mul_comm]

theorem zero_blocks_have_no_support (A : Finset (Fin 3 →₀ ℕ)) :
    honestSupport A (fun _ : Fin 6 ↦ (0 : Leaf K))=∅ := by
  classical
  ext m
  simp [honestSupport,rowSupport]

theorem actual_source_volume_height (p L : ℕ) [Fact p.Prime]
    (a b τ σ : ZMod p) (h₂ : (2 : ZMod p) ≠ 0) (hL : 1 ≤ L)
    (A : Finset (Fin 3 →₀ ℕ))
    (hvol : let N := (honestSupport A (sourceBlocks a b τ σ)).card
      L^N*p^(N-A.card) < p^N) : L^6 < p :=
  short_volume_forces_height p L _ A.card hL (source_honest_support_lower a b τ σ h₂ A) hvol

theorem actual_highest_chart_decode (a b τ σ scalar : K) (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0) :
    σ=(scalar*((((realize (sourceBlocks a b τ σ 5)).coeff 2).coeff 2).coeff 1))/(2*scalar) ∧
    τ=(scalar*((((realize (sourceBlocks a b τ σ 5)).coeff 2).coeff 1).coeff 2))/(2*scalar) := by
  rw [(highest_leaf_chart_anchors a b τ σ).2.1,(highest_leaf_chart_anchors a b τ σ).2.2]
  apply highest_chart_decode scalar τ σ _ _ hl h₂ <;> ring

end ResidualRankActual
