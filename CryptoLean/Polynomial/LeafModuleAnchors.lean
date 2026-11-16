import CryptoLean.Polynomial.RankTwoSourceAnchors
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! Arbitrary leaf multipliers with the original projective grade. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.LeafModuleAnchors
open Polynomial CryptoLean.RankTwoSourceAnchors
variable {R : Type*} [CommRing R]

theorem lowest_mul_coeff (D Q : Polynomial R) (n : ℕ)
    (hlow : ∀ i < n, D.coeff i=0) : (D*Q).coeff n=D.coeff n*Q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (n,0) ?_ ?_
  · intro ij hij hne
    have hs : ij.1+ij.2=n := Finset.mem_antidiagonal.mp hij
    have hi : ij.1 < n := by
      by_contra hn
      apply hne
      apply Prod.ext <;> dsimp <;> omega
    rw [hlow _ hi,zero_mul]
  · intro h
    simp at h

def moduleModel (a b x y V W τ σ : R) (A D : Polynomial R) :
    Polynomial (Polynomial (Polynomial R)) :=
  inTU (C a) (C b) (C x) (C y) X (C V) (C W) A D (C τ) (C σ)

theorem least_leaf_anchors (a b x y V W τ σ : R) (A D : Polynomial R) (n : ℕ)
    (hlow : ∀ i < n, D.coeff i=0) :
    (((moduleModel a b x y V W τ σ A D).coeff 2).coeff 2).coeff n=D.coeff n ∧
    (((moduleModel a b x y V W τ σ A D).coeff 2).coeff 1).coeff n=
      2*D.coeff n*τ*V ∧
    (((moduleModel a b x y V W τ σ A D).coeff 1).coeff 2).coeff n=
      2*D.coeff n*σ*W ∧
    (((moduleModel a b x y V W τ σ A D).coeff 1).coeff 1).coeff n=
      2*D.coeff n*(2*τ*σ-a)*V*W ∧
    (((moduleModel a b x y V W τ σ A D).coeff 1).coeff 0).coeff n=
      2*D.coeff n*(τ^2*σ-a*τ-2*b)*V^2*W := by
  have h := tu_anchors (C a) (C b) (C x) (C y) X (C V) (C W) A D (C τ) (C σ)
  have hC (z : R) : constantCoeff (C z)=z := by simp [constantCoeff]
  have hX : constantCoeff (X : Polynomial R)=0 := by simp [constantCoeff]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp only [moduleModel,h.1]
  · simp only [moduleModel,h.2.1]
    have he : 2*D*(C τ-X)*C V=D*(2*(C τ-X)*C V) := by ring
    rw [he,lowest_mul_coeff D _ n hlow]
    simp only [← constantCoeff_apply,map_mul,map_sub,map_ofNat,hC,hX]
    ring
  · simp only [moduleModel,h.2.2.1]
    have he : 2*D*(C σ-X)*C W=D*(2*(C σ-X)*C W) := by ring
    rw [he,lowest_mul_coeff D _ n hlow]
    simp only [← constantCoeff_apply,map_mul,map_sub,map_ofNat,hC,hX]
    ring
  · simp only [moduleModel,h.2.2.2.1]
    have he : 4*D*C σ*C W*(C τ-X)*C V-2*D*(2*C τ*X+C a+X^2)*C V*C W =
        D*(4*C σ*C W*(C τ-X)*C V-2*(2*C τ*X+C a+X^2)*C V*C W) := by ring
    rw [he,lowest_mul_coeff D _ n hlow]
    simp only [← constantCoeff_apply,map_mul,map_sub,map_add,map_pow,map_ofNat,hC,hX]
    ring
  · simp only [moduleModel,h.2.2.2.2]
    have he : 2*D*C σ*C W*(C τ-X)^2*(C V)^2-
        2*D*((C τ+X)*(C τ*X+C a)+2*C b)*(C V)^2*C W =
        D*(2*C σ*C W*(C τ-X)^2*(C V)^2-
        2*((C τ+X)*(C τ*X+C a)+2*C b)*(C V)^2*C W) := by ring
    rw [he,lowest_mul_coeff D _ n hlow]
    simp only [← constantCoeff_apply,map_mul,map_sub,map_add,map_pow,map_ofNat,hC,hX]
    ring

def lift2Hom : R →+* Polynomial (Polynomial R) :=
  (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)).comp Polynomial.C

theorem lift2Hom_apply (r : R) : lift2Hom r=lift2 r := rfl

def projectiveModule (a b x y τ σ : R) (A D : Polynomial R) :
    Polynomial (Polynomial (Polynomial (Polynomial (Polynomial R)))) :=
  moduleModel (lift2 a) (lift2 b) (lift2 x) (lift2 y) X (C X) (lift2 τ) (lift2 σ)
    (A.map lift2Hom) (D.map lift2Hom)

def takeModuleAnchor
    (f : Polynomial (Polynomial (Polynomial (Polynomial (Polynomial R)))))
    (n t u v w : ℕ) : R := (((((f.coeff t).coeff u).coeff n).coeff v).coeff w)

theorem projective_least_anchors (a b x y τ σ : R) (A D : Polynomial R) (n : ℕ)
    (hlow : ∀ i < n, D.coeff i=0) :
    takeModuleAnchor (projectiveModule a b x y τ σ A D) n 2 2 0 0=D.coeff n ∧
    takeModuleAnchor (projectiveModule a b x y τ σ A D) n 2 1 1 0=2*D.coeff n*τ ∧
    takeModuleAnchor (projectiveModule a b x y τ σ A D) n 1 2 0 1=2*D.coeff n*σ ∧
    takeModuleAnchor (projectiveModule a b x y τ σ A D) n 1 1 1 1=
      2*D.coeff n*(2*τ*σ-a) ∧
    takeModuleAnchor (projectiveModule a b x y τ σ A D) n 1 0 2 1=
      2*D.coeff n*(τ^2*σ-a*τ-2*b) := by
  have hl : ∀ i < n, (D.map lift2Hom).coeff i=0 := by
    intro i hi
    rw [Polynomial.coeff_map,hlow i hi,map_zero]
  have h := least_leaf_anchors (lift2 a) (lift2 b) (lift2 x) (lift2 y) X (C X)
    (lift2 τ) (lift2 σ) (A.map lift2Hom) (D.map lift2Hom) n hl
  simp only [Polynomial.coeff_map,lift2Hom_apply] at h
  simp only [projectiveModule,takeModuleAnchor,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simp [lift2]
  · simp [lift2,mul_assoc]
  · simp [lift2,mul_assoc]
  · simpa [lift2,Polynomial.C_ofNat,map_mul,map_sub,mul_assoc] using
      bihomogeneous_anchor (2*D.coeff n*(2*τ*σ-a)) 1 1
  · have he : 2*lift2 (D.coeff n)*(lift2 τ^2*lift2 σ-lift2 a*lift2 τ-2*lift2 b) =
        lift2 (2*D.coeff n*(τ^2*σ-a*τ-2*b)) := by simp [lift2,Polynomial.C_ofNat]
    rw [he]
    simpa only [pow_one,lift2] using
      bihomogeneous_anchor (2*D.coeff n*(τ^2*σ-a*τ-2*b)) 2 1

variable {ι : Type*} {K : Type*} [Field K]

theorem exists_nonzero_least_leaf (D : Polynomial (MvPolynomial ι K)) (hD : D ≠ 0) :
    ∃ n m, (∀ i < n, D.coeff i=0) ∧ (D.coeff n).coeff m ≠ 0 := by
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero
    (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hD)
  exact ⟨D.natTrailingDegree,m,(fun _ hi ↦ Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi),hm⟩

def leafCode (a b τ σ : K) (x y : MvPolynomial ι K)
    (A D : Polynomial (MvPolynomial ι K)) (n : ℕ) (m : ι →₀ ℕ) : Fin 5 → K :=
  let f := projectiveModule (MvPolynomial.C a) (MvPolynomial.C b) x y
    (MvPolynomial.C τ) (MvPolynomial.C σ) A D
  ![(takeModuleAnchor f n 2 2 0 0).coeff m,
    (takeModuleAnchor f n 2 1 1 0).coeff m,
    (takeModuleAnchor f n 1 2 0 1).coeff m,
    (takeModuleAnchor f n 1 1 1 1).coeff m,
    (takeModuleAnchor f n 1 0 2 1).coeff m]

theorem leafCode_values (a b τ σ : K) (x y : MvPolynomial ι K)
    (A D : Polynomial (MvPolynomial ι K)) (n : ℕ) (m : ι →₀ ℕ)
    (hlow : ∀ i < n, D.coeff i=0) :
    leafCode a b τ σ x y A D n m =
      ![(D.coeff n).coeff m,2*(D.coeff n).coeff m*τ,2*(D.coeff n).coeff m*σ,
        2*(D.coeff n).coeff m*(2*τ*σ-a),
        2*(D.coeff n).coeff m*(τ^2*σ-a*τ-2*b)] := by
  have h := projective_least_anchors (MvPolynomial.C a) (MvPolynomial.C b) x y
    (MvPolynomial.C τ) (MvPolynomial.C σ) A D n hlow
  have hs (z : K) : ((2 : MvPolynomial ι K)*D.coeff n*MvPolynomial.C z).coeff m =
      2*(D.coeff n).coeff m*z := by
    have he : (2 : MvPolynomial ι K)*D.coeff n*MvPolynomial.C z =
        MvPolynomial.C (2*z)*D.coeff n := by
      simp only [map_mul,map_ofNat]
      ring
    rw [he,MvPolynomial.coeff_C_mul]
    ring
  have he : 2*(MvPolynomial.C τ : MvPolynomial ι K)*MvPolynomial.C σ-MvPolynomial.C a =
      MvPolynomial.C (2*τ*σ-a) := by
    simp only [map_sub,map_mul,map_ofNat]
  have hk : (MvPolynomial.C τ : MvPolynomial ι K)^2*MvPolynomial.C σ-MvPolynomial.C a*MvPolynomial.C τ-
      2*MvPolynomial.C b=MvPolynomial.C (τ^2*σ-a*τ-2*b) := by
    simp only [map_sub,map_mul,map_pow,map_ofNat]
  funext i
  fin_cases i <;> simp [leafCode,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,he,hk,hs]
  all_goals
    simp only [map_ofNat]
    first | rw [he] | rw [hk]
    exact hs _

theorem leaf_code_curve_cover (a b τ σ : K) (x y : MvPolynomial ι K)
    (A D : Polynomial (MvPolynomial ι K)) (n : ℕ) (m : ι →₀ ℕ) (S : Finset K)
    (hlow : ∀ i < n, D.coeff i=0) (hμ : (D.coeff n).coeff m ≠ 0)
    (h₂ : (2 : K) ≠ 0) (hS : ∀ i, leafCode a b τ σ x y A D n m i ∈ S) :
    (a,b) ∈ curveCandidates S := by
  have h := leafCode_values a b τ σ x y A D n m hlow
  apply curve_mem_candidates S (leafCode a b τ σ x y A D n m) a b τ σ hS
  · simpa [h] using hμ
  · exact h₂
  all_goals simp [h]

theorem nonzero_module_curve_cover (a b τ σ : K) (x y : MvPolynomial ι K)
    (A D : Polynomial (MvPolynomial ι K)) (S : Finset K) (hD : D ≠ 0)
    (h₂ : (2 : K) ≠ 0)
    (hS : ∀ n m i, leafCode a b τ σ x y A D n m i ∈ S) :
    (a,b) ∈ curveCandidates S := by
  obtain ⟨n,m,hlow,hμ⟩ := exists_nonzero_least_leaf D hD
  exact leaf_code_curve_cover a b τ σ x y A D n m S hlow hμ h₂ (hS n m)

end CryptoLean.LeafModuleAnchors
