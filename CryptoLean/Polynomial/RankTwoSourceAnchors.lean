import CryptoLean.Polynomial.TwoChartCoefficients
import CryptoLean.Polynomial.ShortCoefficientWindows

/-! Curve-dependent two-source combinations. Only source identities; no yield. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.RankTwoSourceAnchors
open Polynomial CryptoLean.CurveParameterElimination
variable {R : Type*} [CommRing R]

def source (a b x y w Z V T W scalar₁ scalar₂ : R) : R :=
  scalar₁*W^2*first a b x y Z V+scalar₂*adjacent a b w Z V T W

theorem original_roots_source_zero (a b x y w Z V T W scalar₁ scalar₂ : R)
    (h₁ : first a b x y Z V=0) (h₂ : adjacent a b w Z V T W=0) :
    source a b x y w Z V T W scalar₁ scalar₂=0 := by
  simp [source,h₁,h₂]

theorem source_scaling (a b x y w Z V T W scalar₁ scalar₂ r s : R) :
    source a b x y w (r*Z) (r*V) (s*T) (s*W) scalar₁ scalar₂ =
      r^2*s^2*source a b x y w Z V T W scalar₁ scalar₂ := by
  unfold source first adjacent
  ring

theorem zero_second_source (a b x y w Z V T W scalar₁ : R) :
    source a b x y w Z V T W scalar₁ 0=scalar₁*W^2*first a b x y Z V := by
  simp [source]

theorem source_b_difference (a b x y w Z V T W scalar₁ scalar₂ : R) :
    source a b x y w Z V T W scalar₁ scalar₂-
      source a 0 x y w Z V T W scalar₁ scalar₂ =
      -4*b*V*W*(scalar₁*W*firstSum x y Z V+scalar₂*adjacentSum w Z V T W) := by
  unfold source first adjacent firstSum adjacentSum
  ring

def inT (a b x y w Z V W scalar₁ scalar₂ σ : R) : Polynomial R :=
  source (C a) (C b) (C x) (C y) (C w) (C Z) (C V)
    (X+C σ*C W) (C W) (C scalar₁) (C scalar₂)

theorem t_coeffs (a b x y w Z V W scalar₁ scalar₂ σ : R) :
    (inT a b x y w Z V W scalar₁ scalar₂ σ).coeff 2 = scalar₂*(Z-w*V)^2 ∧
    (inT a b x y w Z V W scalar₁ scalar₂ σ).coeff 1 =
      2*scalar₂*σ*W*(Z-w*V)^2-
      2*scalar₂*((Z+w*V)*(Z*w+a*V)+2*b*V^2)*W := by
  have he : inT a b x y w Z V W scalar₁ scalar₂ σ =
      C (scalar₂*(Z-w*V)^2)*X^2+
      C (2*scalar₂*σ*W*(Z-w*V)^2-
        2*scalar₂*((Z+w*V)*(Z*w+a*V)+2*b*V^2)*W)*X+
      C (source a b x y w Z V (σ*W) W scalar₁ scalar₂) := by
    simp only [inT,source,first,adjacent,map_add,map_mul,map_sub,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

def inTU (a b x y w V W scalar₁ scalar₂ τ σ : R) : Polynomial (Polynomial R) :=
  inT (C a) (C b) (C x) (C y) (C w) (X+C τ*C V) (C V) (C W)
    (C scalar₁) (C scalar₂) (C σ)

theorem tu_anchors (a b x y w V W scalar₁ scalar₂ τ σ : R) :
    ((inTU a b x y w V W scalar₁ scalar₂ τ σ).coeff 2).coeff 2 = scalar₂ ∧
    ((inTU a b x y w V W scalar₁ scalar₂ τ σ).coeff 2).coeff 1 =
      2*scalar₂*(τ-w)*V ∧
    ((inTU a b x y w V W scalar₁ scalar₂ τ σ).coeff 1).coeff 2 =
      2*scalar₂*(σ-w)*W ∧
    ((inTU a b x y w V W scalar₁ scalar₂ τ σ).coeff 1).coeff 1 =
      4*scalar₂*σ*W*(τ-w)*V-2*scalar₂*(2*τ*w+a+w^2)*V*W ∧
    ((inTU a b x y w V W scalar₁ scalar₂ τ σ).coeff 1).coeff 0 =
      2*scalar₂*σ*W*(τ-w)^2*V^2-
        2*scalar₂*((τ+w)*(τ*w+a)+2*b)*V^2*W := by
  have h := t_coeffs (C a) (C b) (C x) (C y) (C w) (X+C τ*C V)
    (C V) (C W) (C scalar₁) (C scalar₂) (C σ)
  simp only [inTU,h.1,h.2]
  have hq : C scalar₂*(X+C τ*C V-C w*C V)^2 =
      C scalar₂*X^2+C (2*scalar₂*(τ-w)*V)*X+C (scalar₂*(τ-w)^2*V^2) := by
    simp only [map_mul,map_sub,map_pow,map_ofNat]
    ring
  have hl : 2*C scalar₂*C σ*C W*(X+C τ*C V-C w*C V)^2-
      2*C scalar₂*((X+C τ*C V+C w*C V)*((X+C τ*C V)*C w+C a*C V)+
        2*C b*(C V)^2)*C W =
      C (2*scalar₂*(σ-w)*W)*X^2+
      C (4*scalar₂*σ*W*(τ-w)*V-2*scalar₂*(2*τ*w+a+w^2)*V*W)*X+
      C (2*scalar₂*σ*W*(τ-w)^2*V^2-
        2*scalar₂*((τ+w)*(τ*w+a)+2*b)*V^2*W) := by
    simp only [map_add,map_mul,map_sub,map_pow,map_ofNat]
    ring
  rw [hq,hl]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

def inLeafX (a b y w Z V T W scalar₁ scalar₂ : R) : Polynomial R :=
  source (C a) (C b) X (C y) (C w) (C Z) (C V) (C T) (C W)
    (C scalar₁) (C scalar₂)

theorem leaf_x_square (a b y w Z V T W scalar₁ scalar₂ : R) :
    (inLeafX a b y w Z V T W scalar₁ scalar₂).coeff 2 =
      scalar₁*W^2*(Z-y*V)^2 := by
  have hf : first (C a) (C b) X (C y) (C Z) (C V) =
      CryptoLean.EndpointCoefficients.endpointInX a b y Z V 0 := by
    simp only [first,CryptoLean.EndpointCoefficients.endpointInX,zero_mul,add_zero]
  have hg : C scalar₂*adjacent (C a) (C b) (C w) (C Z) (C V) (C T) (C W) =
      C (scalar₂*adjacent a b w Z V T W) := by simp [adjacent,Polynomial.C_ofNat]
  simp only [inLeafX,source,hf,hg,← map_pow,← map_mul,Polynomial.coeff_add,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,CryptoLean.EndpointCoefficients.endpoint_x_square]
  norm_num [sub_eq_add_neg]

def inLeafXY (a b w Z V T W scalar₁ scalar₂ : R) : Polynomial (Polynomial R) :=
  inLeafX (C a) (C b) X (C w) (C Z) (C V) (C T) (C W) (C scalar₁) (C scalar₂)

theorem leaf_xy_anchor (a b w Z V T W scalar₁ scalar₂ : R) :
    ((inLeafXY a b w Z V T W scalar₁ scalar₂).coeff 2).coeff 2 =
      scalar₁*W^2*V^2 := by
  simp only [inLeafXY,leaf_x_square,← map_pow,← map_mul]
  exact (CryptoLean.TwoChartCoefficients.scalar_square_coeffs (scalar₁*W^2) Z V).1

def inWTU (a b x y V W scalar₁ scalar₂ τ σ : R) :
    Polynomial (Polynomial (Polynomial R)) :=
  inTU (C a) (C b) (C x) (C y) X (C V) (C W) (C scalar₁) (C scalar₂) (C τ) (C σ)

theorem constant_leaf_anchors (a b x y V W scalar₁ scalar₂ τ σ : R) :
    (((inWTU a b x y V W scalar₁ scalar₂ τ σ).coeff 2).coeff 2).coeff 0 = scalar₂ ∧
    (((inWTU a b x y V W scalar₁ scalar₂ τ σ).coeff 2).coeff 1).coeff 0 =
      2*scalar₂*τ*V ∧
    (((inWTU a b x y V W scalar₁ scalar₂ τ σ).coeff 1).coeff 2).coeff 0 =
      2*scalar₂*σ*W ∧
    (((inWTU a b x y V W scalar₁ scalar₂ τ σ).coeff 1).coeff 1).coeff 0 =
      2*scalar₂*(2*τ*σ-a)*V*W ∧
    (((inWTU a b x y V W scalar₁ scalar₂ τ σ).coeff 1).coeff 0).coeff 0 =
      2*scalar₂*(τ^2*σ-a*τ-2*b)*V^2*W := by
  have h := tu_anchors (C a) (C b) (C x) (C y) X (C V) (C W)
    (C scalar₁) (C scalar₂) (C τ) (C σ)
  have hC (z : R) : constantCoeff (C z)=z := by simp [constantCoeff]
  have hX : constantCoeff (X : Polynomial R)=0 := by simp [constantCoeff]
  simp only [inWTU,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2]
  simp only [← Polynomial.constantCoeff_apply,map_add,map_mul,map_sub,map_pow,map_ofNat,hC,hX]
  refine ⟨True.intro,?_,?_,?_,?_⟩ <;> ring

theorem bihomogeneous_anchor (k : R) (r s : ℕ) :
    (((C (C k) : Polynomial (Polynomial R))*X^r*(C X)^s).coeff r).coeff s=k := by
  have h : (C (C k) : Polynomial (Polynomial R))*X^r*(C X)^s =
      C (C k*X^s)*X^r := by
    simp only [map_mul,map_pow]
    ring
  rw [h]
  simp only [Polynomial.coeff_C_mul_X_pow,ite_true]

def lift2 (c : R) : Polynomial (Polynomial R) := C (C c)

/-- Outer coordinates are T,U,w,V,W. Leaf x,y are still arbitrary parameters. -/
def projectiveModel (a b x y scalar₁ scalar₂ τ σ : R) :
    Polynomial (Polynomial (Polynomial (Polynomial (Polynomial R)))) :=
  inWTU (lift2 a) (lift2 b) (lift2 x) (lift2 y) X (C X)
    (lift2 scalar₁) (lift2 scalar₂) (lift2 τ) (lift2 σ)

def takeAnchor (f : Polynomial (Polynomial (Polynomial (Polynomial (Polynomial R)))))
    (t u v w : ℕ) : R := (((((f.coeff t).coeff u).coeff 0).coeff v).coeff w)

theorem exact_projective_anchors (a b x y scalar₁ scalar₂ τ σ : R) :
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 2 2 0 0=scalar₂ ∧
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 2 1 1 0=2*scalar₂*τ ∧
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 2 0 1=2*scalar₂*σ ∧
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 1 1 1=
      2*scalar₂*(2*τ*σ-a) ∧
    takeAnchor (projectiveModel a b x y scalar₁ scalar₂ τ σ) 1 0 2 1=
      2*scalar₂*(τ^2*σ-a*τ-2*b) := by
  have h := constant_leaf_anchors (lift2 a) (lift2 b) (lift2 x) (lift2 y) X (C X)
    (lift2 scalar₁) (lift2 scalar₂) (lift2 τ) (lift2 σ)
  simp only [projectiveModel,takeAnchor,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [lift2]
  · simp [lift2,mul_assoc]
  · simp [lift2,mul_assoc]
  · simpa [lift2,Polynomial.C_ofNat,map_mul,map_sub,mul_assoc] using
      bihomogeneous_anchor (2*scalar₂*(2*τ*σ-a)) 1 1
  · have he : 2*lift2 scalar₂*(lift2 τ^2*lift2 σ-lift2 a*lift2 τ-2*lift2 b) =
        lift2 (2*scalar₂*(τ^2*σ-a*τ-2*b)) := by simp [lift2,Polynomial.C_ofNat]
    rw [he]
    simpa only [pow_one,lift2] using
      bihomogeneous_anchor (2*scalar₂*(τ^2*σ-a*τ-2*b)) 2 1

variable {K : Type*} [Field K]

theorem decode_curve_and_charts (a b τ σ μ c d e k : K)
    (hμ : μ ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hc : c=2*μ*τ) (hd : d=2*μ*σ)
    (he : e=2*μ*(2*τ*σ-a)) (hk : k=2*μ*(τ^2*σ-a*τ-2*b)) :
    τ=c/(2*μ) ∧ σ=d/(2*μ) ∧ a=2*τ*σ-e/(2*μ) ∧
      b=(τ^2*σ-a*τ-k/(2*μ))/2 := by
  have hn := mul_ne_zero h₂ hμ
  have hc' : c/(2*μ)=τ := (div_eq_iff hn).2 (by rw [hc]; ring)
  have hd' : d/(2*μ)=σ := (div_eq_iff hn).2 (by rw [hd]; ring)
  have he' : e/(2*μ)=2*τ*σ-a := (div_eq_iff hn).2 (by rw [he]; ring)
  have hk' : k/(2*μ)=τ^2*σ-a*τ-2*b := (div_eq_iff hn).2 (by rw [hk]; ring)
  refine ⟨hc'.symm,hd'.symm,?_,?_⟩
  · linear_combination he'
  · apply (eq_div_iff h₂).2
    linear_combination hk'

def curveCode (q : Fin 5 → K) : K × K :=
  let τ := q 1/(2*q 0)
  let σ := q 2/(2*q 0)
  let a := 2*τ*σ-q 3/(2*q 0)
  (a,(τ^2*σ-a*τ-q 4/(2*q 0))/2)

theorem curveCode_eq (q : Fin 5 → K) (a b τ σ : K)
    (hμ : q 0 ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hc : q 1=2*q 0*τ) (hd : q 2=2*q 0*σ)
    (he : q 3=2*q 0*(2*τ*σ-a)) (hk : q 4=2*q 0*(τ^2*σ-a*τ-2*b)) :
    curveCode q=(a,b) := by
  rcases decode_curve_and_charts a b τ σ (q 0) (q 1) (q 2) (q 3) (q 4)
    hμ h₂ hc hd he hk with ⟨ht,hs,ha,hb⟩
  dsimp [curveCode]
  rw [← ht,← hs,← ha,← hb]

def curveCandidates (S : Finset K) : Finset (K × K) := by
  classical
  exact ((Finset.univ : Finset (Fin 5 → S)).filter (fun q ↦ (q 0 : K) ≠ 0)).image
    (fun q ↦ curveCode (fun i ↦ (q i : K)))

theorem curveCandidates_card_le (S : Finset K) :
    (curveCandidates S).card ≤ S.card^5 := by
  classical
  calc
    _ ≤ ((Finset.univ : Finset (Fin 5 → S)).filter (fun q ↦ (q 0 : K) ≠ 0)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin 5 → S)).card := Finset.card_filter_le _ _
    _ = S.card^5 := by simp

theorem curve_mem_candidates (S : Finset K) (q : Fin 5 → K) (a b τ σ : K)
    (hq : ∀ i, q i ∈ S) (hμ : q 0 ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hc : q 1=2*q 0*τ) (hd : q 2=2*q 0*σ)
    (he : q 3=2*q 0*(2*τ*σ-a)) (hk : q 4=2*q 0*(τ^2*σ-a*τ-2*b)) :
    (a,b) ∈ curveCandidates S := by
  classical
  refine Finset.mem_image.mpr ⟨(fun i ↦ ⟨q i,hq i⟩),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hμ⟩
  · exact curveCode_eq q a b τ σ hμ h₂ hc hd he hk

theorem curveWindow_card_le [DecidableEq K] (T : ℕ) :
    (curveCandidates (CryptoLean.FieldRectangles.intWindow K T)).card ≤ (2*T+1)^5 :=
  (curveCandidates_card_le _).trans (Nat.pow_le_pow_left
    (CryptoLean.FieldRectangles.intWindow_card_le T) 5)

end CryptoLean.RankTwoSourceAnchors
