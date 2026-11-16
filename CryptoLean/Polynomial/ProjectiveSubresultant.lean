import CryptoLean.Polynomial.RankTwoSourceAnchors

/-! A finite-chart adjacent-quadratic subresultant, with all exceptional branches. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.ProjectiveSubresultant
open Polynomial CryptoLean.CurveParameterElimination
variable {R : Type*} [CommRing R]

def firstLinear (a b x y : R) : R := (x+y)*(x*y+a)+2*b
def firstConstant (a b x y : R) : R := (x*y-a)^2-4*b*(x+y)
def adjacentLinear (a b w T W : R) : R :=
  w*T^2+(a+w^2)*T*W+(a*w+2*b)*W^2
def adjacentConstant (a b w T W : R) : R :=
  w^2*T^2-2*(a*w+2*b)*T*W+(a^2-4*b*w)*W^2

def residual (a b x y w Z V T W : R) : R :=
  2*(firstLinear a b x y*(T-w*W)^2-(x-y)^2*adjacentLinear a b w T W)*Z+
    ((x-y)^2*adjacentConstant a b w T W-(T-w*W)^2*firstConstant a b x y)*V

theorem exact_subresultant (a b x y w Z V T W : R) :
    (x-y)^2*adjacent a b w Z V T W-(T-w*W)^2*first a b x y Z V =
      V*residual a b x y w Z V T W := by
  unfold residual firstLinear firstConstant adjacentLinear adjacentConstant first adjacent
  ring

theorem residual_scaling (a b x y w Z V T W r s : R) :
    residual a b x y w (r*Z) (r*V) (s*T) (s*W) =
      r*s^2*residual a b x y w Z V T W := by
  unfold residual firstLinear firstConstant adjacentLinear adjacentConstant
  ring

theorem diagonal_identity (a b x w Z V T W : R) :
    V*residual a b x x w Z V T W = -(T-w*W)^2*first a b x x Z V := by
  have h := exact_subresultant a b x x w Z V T W
  simpa only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_mul,zero_sub,neg_mul] using h.symm

variable {K : Type*} [Field K]

theorem original_roots_residual_zero (a b x y w Z V T W : K) (hV : V ≠ 0)
    (h₁ : first a b x y Z V=0) (h₂ : adjacent a b w Z V T W=0) :
    residual a b x y w Z V T W=0 := by
  have h := exact_subresultant a b x y w Z V T W
  rw [h₁,h₂,mul_zero,mul_zero,sub_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hV

theorem retained_residual_equiv (a b x y w Z V T W : K) (hV : V ≠ 0) (hxy : x ≠ y) :
    (first a b x y Z V=0 ∧ residual a b x y w Z V T W=0) ↔
      (first a b x y Z V=0 ∧ adjacent a b w Z V T W=0) := by
  constructor
  · rintro ⟨h₁,hR⟩
    have h := exact_subresultant a b x y w Z V T W
    rw [h₁,hR,mul_zero,mul_zero,sub_zero] at h
    exact ⟨h₁,(mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hxy))⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁,original_roots_residual_zero a b x y w Z V T W hV h₁ h₂⟩

theorem complete_branch_split (a b x y w Z V T W : K) :
    (first a b x y Z V=0 ∧ adjacent a b w Z V T W=0) ↔
      (V ≠ 0 ∧ x ≠ y ∧ first a b x y Z V=0 ∧ residual a b x y w Z V T W=0) ∨
      ((V=0 ∨ x=y) ∧ first a b x y Z V=0 ∧ adjacent a b w Z V T W=0) := by
  by_cases hV : V=0
  · simp [hV]
  by_cases hxy : x=y
  · simp [hxy]
  simpa [hV,hxy] using (retained_residual_equiv a b x y w Z V T W hV hxy).symm

theorem diagonal_residual_zero (a b x w Z V T W : K) (hV : V ≠ 0)
    (h₁ : first a b x x Z V=0) : residual a b x x w Z V T W=0 := by
  have h := diagonal_identity a b x w Z V T W
  rw [h₁,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hV

def inLeafX (a b y w Z V T W : R) : Polynomial R :=
  residual (C a) (C b) X (C y) (C w) (C Z) (C V) (C T) (C W)

theorem leaf_x_square (a b y w Z V T W : R) :
    (inLeafX a b y w Z V T W).coeff 2 =
      2*(y*(T-w*W)^2-adjacentLinear a b w T W)*Z+
        (adjacentConstant a b w T W-(T-w*W)^2*y^2)*V := by
  let q := 2*(y*(T-w*W)^2-adjacentLinear a b w T W)*Z+
    (adjacentConstant a b w T W-(T-w*W)^2*y^2)*V
  have hj : adjacentLinear (C a) (C b) (C w) (C T) (C W) =
      C (adjacentLinear a b w T W) := by simp [adjacentLinear,Polynomial.C_ofNat]
  have hm : adjacentConstant (C a) (C b) (C w) (C T) (C W) =
      C (adjacentConstant a b w T W) := by simp [adjacentConstant,Polynomial.C_ofNat]
  have he : inLeafX a b y w Z V T W = C q*X^2+
      C (residual a b 1 y w Z V T W-residual a b 0 y w Z V T W-q)*X+
      C (residual a b 0 y w Z V T W) := by
    simp only [inLeafX,residual,firstLinear,firstConstant,hj,hm,q,
      map_add,map_sub,map_mul,map_pow,map_ofNat,map_zero,map_one]
    ring
  rw [he]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C]
  norm_num [q]

def inLeafXY (a b w Z V T W : R) : Polynomial (Polynomial R) :=
  inLeafX (C a) (C b) X (C w) (C Z) (C V) (C T) (C W)

theorem leaf_xy_coeffs (a b w Z V T W : R) :
    ((inLeafXY a b w Z V T W).coeff 2).coeff 2 = -(T-w*W)^2*V ∧
    ((inLeafXY a b w Z V T W).coeff 2).coeff 1 = 2*(T-w*W)^2*Z ∧
    ((inLeafXY a b w Z V T W).coeff 2).coeff 0 =
      -2*adjacentLinear a b w T W*Z+adjacentConstant a b w T W*V := by
  have hj : adjacentLinear (C a) (C b) (C w) (C T) (C W) =
      C (adjacentLinear a b w T W) := by simp [adjacentLinear,Polynomial.C_ofNat]
  have hm : adjacentConstant (C a) (C b) (C w) (C T) (C W) =
      C (adjacentConstant a b w T W) := by simp [adjacentConstant,Polynomial.C_ofNat]
  simp only [inLeafXY,leaf_x_square,hj,hm]
  have he : 2*(X*(C T-C w*C W)^2-C (adjacentLinear a b w T W))*C Z+
      (C (adjacentConstant a b w T W)-(C T-C w*C W)^2*X^2)*C V =
      C (-(T-w*W)^2*V)*X^2+C (2*(T-w*W)^2*Z)*X+
      C (-2*adjacentLinear a b w T W*Z+adjacentConstant a b w T W*V) := by
    simp only [map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat]
    ring
  rw [he]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

def leafModel (a b Z V T W : R) : Polynomial (Polynomial (Polynomial R)) :=
  inLeafXY (C a) (C b) X (C Z) (C V) (C T) (C W)

theorem leaf_anchors (a b Z V T W : R) :
    (((leafModel a b Z V T W).coeff 2).coeff 2).coeff 0 = -V*T^2 ∧
    (((leafModel a b Z V T W).coeff 2).coeff 1).coeff 0 = 2*Z*T^2 ∧
    (((leafModel a b Z V T W).coeff 2).coeff 0).coeff 0 =
      -2*(a*T*W+2*b*W^2)*Z+(a^2*W^2-4*b*T*W)*V := by
  have h := leaf_xy_coeffs (C a) (C b) X (C Z) (C V) (C T) (C W)
  have hC (z : R) : constantCoeff (C z)=z := by simp [constantCoeff]
  have hX : constantCoeff (X : Polynomial R)=0 := by simp [constantCoeff]
  simp only [leafModel,h.1,h.2.1,h.2.2]
  simp only [← constantCoeff_apply,adjacentLinear,adjacentConstant,map_mul,map_sub,map_add,
    map_pow,map_neg,map_ofNat,hC,hX]
  refine ⟨?_,?_,?_⟩ <;> ring

open CryptoLean.TwoChartCoefficients

def coefficient4 (f : P4 R) (u x v w : ℕ) : R := (((f.coeff u).coeff x).coeff v).coeff w

theorem projective_anchor_forms (a b τ σ : R) :
    coefficient4 (-vVar*(xVar+lift4 σ*wVar)^2 : P4 R) 0 2 1 0 = -1 ∧
    coefficient4 (-vVar*(xVar+lift4 σ*wVar)^2 : P4 R) 0 1 1 1 = -2*σ ∧
    coefficient4 (2*(uVar+lift4 τ*vVar)*(xVar+lift4 σ*wVar)^2 : P4 R) 0 2 1 0 = 2*τ ∧
    coefficient4 (-2*(lift4 a*(xVar+lift4 σ*wVar)*wVar+2*lift4 b*wVar^2)*
      (uVar+lift4 τ*vVar)+(lift4 a^2*wVar^2-4*lift4 b*(xVar+lift4 σ*wVar)*wVar)*vVar : P4 R)
      1 1 0 1 = -2*a ∧
    coefficient4 (-2*(lift4 a*(xVar+lift4 σ*wVar)*wVar+2*lift4 b*wVar^2)*
      (uVar+lift4 τ*vVar)+(lift4 a^2*wVar^2-4*lift4 b*(xVar+lift4 σ*wVar)*wVar)*vVar : P4 R)
      1 0 0 2 = -2*a*σ-4*b := by
  let e : P4 R →+* Polynomial (Polynomial (Polynomial R)) := Polynomial.constantCoeff
  have hu : e uVar=0 := by simp [e,uVar,Polynomial.constantCoeff]
  have hx : e xVar=X := by simp [e,xVar,Polynomial.constantCoeff]
  have hv : e vVar=C X := by simp [e,vVar,Polynomial.constantCoeff]
  have hw : e wVar=C (C X) := by simp [e,wVar,Polynomial.constantCoeff]
  have hl (c : R) : e (lift4 c)=C (C (C c)) := by simp [e,lift4,Polynomial.constantCoeff]
  let v : Polynomial (Polynomial (Polynomial R)) := C X
  let w : Polynomial (Polynomial (Polynomial R)) := C (C X)
  let t : Polynomial (Polynomial (Polynomial R)) := X+C (C (C σ))*w
  let g : Polynomial (Polynomial (Polynomial R)) :=
    -2*(C (C (C a))*t*w+2*C (C (C b))*w^2)
  let h : Polynomial (Polynomial (Polynomial R)) :=
    g*(C (C (C τ))*v)+(C (C (C a))^2*w^2-4*C (C (C b))*t*w)*v
  let f : P4 R := -2*(lift4 a*(xVar+lift4 σ*wVar)*wVar+2*lift4 b*wVar^2)*
    (uVar+lift4 τ*vVar)+(lift4 a^2*wVar^2-4*lift4 b*(xVar+lift4 σ*wVar)*wVar)*vVar
  have cn (z : Polynomial (Polynomial (Polynomial R))) :
      (C (-z) : P4 R) = -C z := by
    apply eq_neg_iff_add_eq_zero.mpr
    have hz : -z+z=0 := by ring
    rw [← map_add,hz,map_zero]
  have cs (z q : Polynomial (Polynomial (Polynomial R))) :
      (C (z-q) : P4 R) = C z-C q := by
    apply eq_sub_iff_add_eq.mpr
    have hz : z-q+q=z := by ring
    rw [← map_add,hz]
  have hf : f=C g*X+C h := by
    simp only [f,g,h,t,v,w,lift4,uVar,xVar,vVar,wVar,map_add,map_mul,map_pow,
      cn,cs,map_ofNat]
    norm_num [Polynomial.C_ofNat]
    ring
  have h₁ : f.coeff 1=g := by
    rw [hf]
    simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
    norm_num
  refine ⟨?_,?_,?_,?_,?_⟩
  · change (((e (-vVar*(xVar+lift4 σ*wVar)^2)).coeff 2).coeff 1).coeff 0 = -1
    simp only [map_neg,map_mul,map_pow,map_add,hv,hx,hl,hw]
    norm_num [pow_two,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero]
  · change (((e (-vVar*(xVar+lift4 σ*wVar)^2)).coeff 1).coeff 1).coeff 1 = -2*σ
    simp only [map_neg,map_mul,map_pow,map_add,hv,hx,hl,hw]
    norm_num [pow_two,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero]
    ring
  · change (((e (2*(uVar+lift4 τ*vVar)*(xVar+lift4 σ*wVar)^2)).coeff 2).coeff 1).coeff 0 = 2*τ
    simp only [map_mul,map_pow,map_add,map_ofNat,hu,hv,hx,hl,hw,zero_add]
    norm_num [pow_two,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero]
  · change (((f.coeff 1).coeff 1).coeff 0).coeff 1 = -2*a
    rw [h₁]
    norm_num [g,t,v,w,pow_two,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero]
  · change (((f.coeff 1).coeff 0).coeff 0).coeff 2 = -2*a*σ-4*b
    rw [h₁]
    norm_num [g,t,v,w,pow_two,Polynomial.coeff_mul,Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero]
    ring

def shiftedResidual (a b τ σ : R) : Polynomial (Polynomial (Polynomial (P4 R))) :=
  leafModel (lift4 a) (lift4 b) (uVar+lift4 τ*vVar) vVar (xVar+lift4 σ*wVar) wVar

theorem exact_source_anchors (a b τ σ : R) :
    coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 2).coeff 0) 0 2 1 0 = -1 ∧
    coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 2).coeff 0) 0 1 1 1 = -2*σ ∧
    coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 1).coeff 0) 0 2 1 0 = 2*τ ∧
    coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 0).coeff 0) 1 1 0 1 = -2*a ∧
    coefficient4 ((((shiftedResidual a b τ σ).coeff 2).coeff 0).coeff 0) 1 0 0 2 = -2*a*σ-4*b := by
  have h := leaf_anchors (lift4 a) (lift4 b) (uVar+lift4 τ*vVar) vVar
    (xVar+lift4 σ*wVar) wVar
  simpa only [shiftedResidual,h.1,h.2.1,h.2.2] using projective_anchor_forms a b τ σ

theorem recover_source_parameters (scalar τ σ a b c d e k : K)
    (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hc : c=-2*scalar*σ) (hd : d=2*scalar*τ)
    (he : e=-2*scalar*a) (hk : k=scalar*(-2*a*σ-4*b)) :
    τ=d/(2*scalar) ∧ σ=-c/(2*scalar) ∧ a=-e/(2*scalar) ∧
      b=-(k+2*scalar*a*σ)/(4*scalar) := by
  have hn := mul_ne_zero h₂ hl
  have h₄ : (4 : K)=2*2 := by ring
  have hn₄ : (4 : K)*scalar ≠ 0 := by rw [h₄]; exact mul_ne_zero (mul_ne_zero h₂ h₂) hl
  refine ⟨?_,?_,?_,?_⟩
  · apply (eq_div_iff hn).2
    rw [hd]
    ring
  · apply (eq_div_iff hn).2
    rw [hc]
    ring
  · apply (eq_div_iff hn).2
    rw [he]
    ring
  · apply (eq_div_iff hn₄).2
    rw [hk]
    ring

def modelCode (q : Fin 4 → K) : K × K :=
  let scalar := -q 0
  let σ := -q 1/(2*scalar)
  let a := -q 2/(2*scalar)
  (a,-(q 3+2*scalar*a*σ)/(4*scalar))

theorem modelCode_eq (q : Fin 4 → K) (scalar σ a b : K)
    (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0) (hq : q 0=-scalar)
    (hc : q 1=-2*scalar*σ) (he : q 2=-2*scalar*a) (hk : q 3=scalar*(-2*a*σ-4*b)) :
    modelCode q=(a,b) := by
  rcases recover_source_parameters scalar 0 σ a b (q 1) 0 (q 2) (q 3) hl h₂ hc
    (by ring) he hk with ⟨_,hs,ha,hb⟩
  dsimp [modelCode]
  rw [hq,neg_neg,← hs,← ha,← hb]

def modelCandidates (S : Finset K) : Finset (K × K) := by
  classical
  exact ((Finset.univ : Finset (Fin 4 → S)).filter (fun q ↦ (q 0 : K) ≠ 0)).image
    (fun q ↦ modelCode (fun i ↦ (q i : K)))

theorem modelCandidates_card_le (S : Finset K) : (modelCandidates S).card ≤ S.card^4 := by
  classical
  calc
    _ ≤ ((Finset.univ : Finset (Fin 4 → S)).filter (fun q ↦ (q 0 : K) ≠ 0)).card :=
      Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin 4 → S)).card := Finset.card_filter_le _ _
    _ = S.card^4 := by simp

theorem model_curve_cover (S : Finset K) (q : Fin 4 → K) (scalar σ a b : K)
    (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0) (hS : ∀ i, q i ∈ S) (hq : q 0=-scalar)
    (hc : q 1=-2*scalar*σ) (he : q 2=-2*scalar*a) (hk : q 3=scalar*(-2*a*σ-4*b)) :
    (a,b) ∈ modelCandidates S := by
  classical
  refine Finset.mem_image.mpr ⟨(fun i ↦ ⟨q i,hS i⟩),?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change q 0 ≠ 0
    rw [hq]
    exact neg_ne_zero.mpr hl
  · exact modelCode_eq q scalar σ a b hl h₂ hq hc he hk

theorem modelWindow_card_le [DecidableEq K] (T : ℕ) :
    (modelCandidates (CryptoLean.FieldRectangles.intWindow K T)).card ≤ (2*T+1)^4 :=
  (modelCandidates_card_le _).trans (Nat.pow_le_pow_left
    (CryptoLean.FieldRectangles.intWindow_card_le T) 4)

theorem profile_capacity_square (p H₁ H₂ A B : ℕ)
    (hA : A ≤ p) (hH : A ≤ 9*H₁^2) (hB : B ≤ 9*H₂^2)
    (hshort : H₁*H₂^2 < p) : (A*B)^2 < 729*p^3 := by
  have hA₂ : A^2 ≤ 9*p*H₁^2 := by
    have h := Nat.mul_le_mul hA hH
    nlinarith
  have hB₂ : B^2 ≤ 81*H₂^4 := by
    have h := Nat.pow_le_pow_left hB 2
    nlinarith
  have hcap : (A*B)^2 ≤ 729*p*(H₁*H₂^2)^2 := by
    have h := Nat.mul_le_mul hA₂ hB₂
    nlinarith
  have hp : 0 < p := Nat.zero_lt_of_lt hshort
  have hsq : (H₁*H₂^2)^2 < p^2 := Nat.pow_lt_pow_left hshort (by decide : 2 ≠ 0)
  have hstrict := Nat.mul_lt_mul_of_pos_left hsq (by omega : 0 < 729*p)
  nlinarith

theorem universal_cover_charge (p Q A B : ℕ) (hp : 0 < p)
    (hcover : p^2 ≤ Q*(A*B)) (hcap : (A*B)^2 < 729*p^3) : p < 729*Q^2 := by
  by_contra hn
  have hQ : 729*Q^2 ≤ p := by omega
  have hpos : 0 < Q := by
    by_contra hz
    have : Q=0 := by omega
    simp [this] at hcover
    nlinarith
  have hlo : p^4 ≤ Q^2*(A*B)^2 := by
    have h := Nat.pow_le_pow_left hcover 2
    nlinarith
  have hhi := Nat.mul_lt_mul_of_pos_left hcap (by positivity : 0 < Q^2)
  have hu := Nat.mul_le_mul_right (p^3) hQ
  nlinarith

end CryptoLean.ProjectiveSubresultant
