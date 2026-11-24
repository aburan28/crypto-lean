import CryptoLean.Polynomial.RankTwoSourceAnchors

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.RankTwoSourceAnchors

namespace RankTwoActual
variable {K : Type*} [Field K]

def actualCode (a b x y scalar₁ scalar₂ τ σ : K) : Fin 5 → K :=
  ![takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 2 2 0 0,
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 2 1 1 0,
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 2 0 1,
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 1 1 1,
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 0 2 1]

theorem actual_curve_in_candidates (a b x y scalar₁ scalar₂ τ σ : K)
    (S : Finset K) (hS : ∀ i, actualCode a b x y scalar₁ scalar₂ τ σ i ∈ S)
    (hμ : scalar₂ ≠ 0) (h₂ : (2 : K) ≠ 0) : (a,b) ∈ curveCandidates S := by
  have h := exact_projective_anchors a b x y scalar₁ scalar₂ τ σ
  apply curve_mem_candidates S (actualCode a b x y scalar₁ scalar₂ τ σ) a b τ σ hS
  · simpa [actualCode,h.1] using hμ
  · exact h₂
  · simp [actualCode,h.1,h.2.1]
  · simp [actualCode,h.1,h.2.2.1]
  · simp [actualCode,h.1,h.2.2.2.1]
  · simp [actualCode,h.1,h.2.2.2.2]

theorem equal_codes_same_curve (a b a' b' x y x' y' scalar₁ scalar₂ τ σ
    scalar₁' scalar₂' τ' σ' : K)
    (hμ : scalar₂ ≠ 0) (hμ' : scalar₂' ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hcode : actualCode a b x y scalar₁ scalar₂ τ σ =
      actualCode a' b' x' y' scalar₁' scalar₂' τ' σ') : a=a' ∧ b=b' := by
  have identify (a b x y l m t s : K) (hm : m ≠ 0) :
      curveCode (actualCode a b x y l m t s)=(a,b) := by
    have h := exact_projective_anchors a b x y l m t s
    apply curveCode_eq _ a b t s
    · simpa [actualCode,h.1] using hm
    · exact h₂
    · simp [actualCode,h.1,h.2.1]
    · simp [actualCode,h.1,h.2.2.1]
    · simp [actualCode,h.1,h.2.2.2.1]
    · simp [actualCode,h.1,h.2.2.2.2]
  have hp := (identify a b x y scalar₁ scalar₂ τ σ hμ).symm.trans
    ((congrArg curveCode hcode).trans (identify a' b' x' y' scalar₁' scalar₂' τ' σ' hμ'))
  exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩

theorem zero_second_free_chart (a b x y w U V X W scalar₁ τ σ σ' : K) :
    source a b x y w (U+τ*V) V (X+σ*W) W scalar₁ 0 =
      source a b x y w (U+τ*V) V (X+σ'*W) W scalar₁ 0 := by
  rw [zero_second_source,zero_second_source]

theorem bounded_integer_anchors_cover (p T : ℕ) [Fact p.Prime]
    (a b x y scalar₁ scalar₂ τ σ : ZMod p) (r : Fin 5 → ℤ)
    (hμ : scalar₂ ≠ 0) (h₂ : (2 : ZMod p) ≠ 0)
    (hr : ∀ i, (r i : ZMod p)=actualCode a b x y scalar₁ scalar₂ τ σ i)
    (hT : ∀ i, (r i).natAbs ≤ T) :
    (a,b) ∈ curveCandidates (CryptoLean.FieldRectangles.intWindow (ZMod p) T) := by
  apply actual_curve_in_candidates a b x y scalar₁ scalar₂ τ σ _ ?_ hμ h₂
  intro i
  rw [← hr i]
  exact CryptoLean.FieldRectangles.mem_intWindow_of_bounds T (r i)
    (CryptoLean.ShortCoefficientWindows.integer_bounds_of_natAbs T (r i) (hT i))

end RankTwoActual
