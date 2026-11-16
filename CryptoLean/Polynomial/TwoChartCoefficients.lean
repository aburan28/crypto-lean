import CryptoLean.Polynomial.CurveParameterElimination

/-! Exact three-anchor source extraction for the primitive adjacent combination.
No selector runtime, completeness or useful-yield claim. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.TwoChartCoefficients
open Polynomial CryptoLean.CurveParameterElimination CryptoLean.EndpointCoefficients
variable {R : Type*} [CommRing R]

def inX (a b y w Z V T W : R) : Polynomial R :=
  primitive (C a) (C b) X (C y) (C w) (C Z) (C V) (C T) (C W)

theorem x_square (a b y w Z V T W : R) :
    (inX a b y w Z V T W).coeff 2 = adjacentSum w Z V T W*W*(Z-y*V)^2 := by
  have hf : first (C a) (C b) X (C y) (C Z) (C V) =
      endpointInX a b y Z V 0 := by
    simp only [first,endpointInX,zero_mul,add_zero]
  have ha : adjacentSum (C w) (C Z) (C V) (C T) (C W) =
      C (adjacentSum w Z V T W) := by simp [adjacentSum]
  have hg : adjacent (C a) (C b) (C w) (C Z) (C V) (C T) (C W) =
      C (adjacent a b w Z V T W) := by simp [adjacent,Polynomial.C_ofNat]
  have hs : firstSum X (C y) (C Z) (C V) = C V*X+C (Z+y*V) := by
    simp only [firstSum,map_add,map_mul]
    ring
  simp only [inX,primitive,hf,ha,hg,hs,← map_mul,Polynomial.coeff_sub,
    Polynomial.coeff_C_mul,Polynomial.coeff_mul_C,Polynomial.coeff_add,
    Polynomial.coeff_C,endpoint_x_square]
  norm_num [Polynomial.coeff_X,sub_eq_add_neg]

theorem scalar_square_coeffs (k Z V : R) :
    (C k*(C Z-X*C V)^2).coeff 2 = k*V^2 ∧
    (C k*(C Z-X*C V)^2).coeff 1 = -2*k*Z*V := by
  have h : C k*(C Z-X*C V)^2 =
      C (k*V^2)*X^2+C (-2*k*Z*V)*X+C (k*Z^2) := by
    simp only [map_neg,map_mul,map_pow,map_ofNat]
    ring
  rw [h]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

def inXY (a b w Z V T W : R) : Polynomial (Polynomial R) :=
  inX (C a) (C b) X (C w) (C Z) (C V) (C T) (C W)

theorem xy_coeffs (a b w Z V T W : R) :
    ((inXY a b w Z V T W).coeff 2).coeff 2 = adjacentSum w Z V T W*W*V^2 ∧
    ((inXY a b w Z V T W).coeff 2).coeff 1 = -2*adjacentSum w Z V T W*W*Z*V := by
  simp only [inXY,x_square]
  have hc : adjacentSum (C w) (C Z) (C V) (C T) (C W)*C W =
      C (adjacentSum w Z V T W*W) := by simp [adjacentSum]
  rw [hc]
  simpa [mul_assoc] using scalar_square_coeffs (adjacentSum w Z V T W*W) Z V

def leafModel (a b Z V T W : R) : Polynomial (Polynomial (Polynomial R)) :=
  inXY (C a) (C b) X (C Z) (C V) (C T) (C W)

theorem leaf_anchors (a b Z V T W : R) :
    (((leafModel a b Z V T W).coeff 2).coeff 2).coeff 1 = V^3*W^2 ∧
    (((leafModel a b Z V T W).coeff 2).coeff 1).coeff 1 = -2*Z*V^2*W^2 ∧
    (((leafModel a b Z V T W).coeff 2).coeff 2).coeff 0 = (Z*W+T*V)*W*V^2 := by
  have h := xy_coeffs (C a) (C b) X (C Z) (C V) (C T) (C W)
  simp only [leafModel,h.1,h.2]
  have h₁ : adjacentSum X (C Z) (C V) (C T) (C W)*C W*(C V)^2 =
      C (V^3*W^2)*X+C ((Z*W+T*V)*W*V^2) := by
    simp only [adjacentSum,map_add,map_mul,map_pow]
    ring
  have h₂ : -2*adjacentSum X (C Z) (C V) (C T) (C W)*C W*C Z*C V =
      C (-2*Z*V^2*W^2)*X+C (-2*(Z*W+T*V)*W*Z*V) := by
    simp only [adjacentSum,map_add,map_neg,map_mul,map_pow,map_ofNat]
    ring
  rw [h₁,h₂]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

theorem shifted_leaf_anchors (a b U X V W τ σ : R) :
    (((leafModel a b (U+τ*V) V (X+σ*W) W).coeff 2).coeff 2).coeff 1 = V^3*W^2 ∧
    (((leafModel a b (U+τ*V) V (X+σ*W) W).coeff 2).coeff 1).coeff 1 =
      -2*U*V^2*W^2+(-2*τ)*V^3*W^2 ∧
    (((leafModel a b (U+τ*V) V (X+σ*W) W).coeff 2).coeff 2).coeff 0 =
      U*V^2*W^2+X*V^3*W+(τ+σ)*V^3*W^2 := by
  rcases leaf_anchors a b (U+τ*V) V (X+σ*W) W with ⟨h₁,h₂,h₃⟩
  rw [h₁,h₂,h₃]
  constructor
  · rfl
  constructor <;> ring

abbrev P4 (R : Type*) [CommRing R] := Polynomial (Polynomial (Polynomial (Polynomial R)))
instance p4CommRing : CommRing (P4 R) := by
  change CommRing (Polynomial (Polynomial (Polynomial (Polynomial R))))
  exact @Polynomial.commRing (Polynomial (Polynomial (Polynomial R)))
    (@Polynomial.commRing (Polynomial (Polynomial R))
      (@Polynomial.commRing (Polynomial R) (@Polynomial.commRing R inferInstance)))
def lift4 (c : R) : P4 R := C (C (C (C c)))
def uVar : P4 R := X
def xVar : P4 R := C X
def vVar : P4 R := C (C X)
def wVar : P4 R := C (C (C X))

/-- Extract U⁰ X⁰ V³ W². -/
def projectiveAnchor (f : P4 R) : R := (((f.coeff 0).coeff 0).coeff 3).coeff 2

theorem projective_anchor (A B C₀ : R) :
    projectiveAnchor (lift4 A*uVar*vVar^2*wVar^2+
      lift4 B*xVar*vVar^3*wVar+lift4 C₀*vVar^3*wVar^2) = C₀ := by
  let e : P4 R →+* Polynomial (Polynomial R) :=
    (Polynomial.constantCoeff : Polynomial (Polynomial (Polynomial R)) →+*
      Polynomial (Polynomial R)).comp Polynomial.constantCoeff
  have hu : e uVar=0 := by simp [e,uVar,Polynomial.constantCoeff]
  have hx : e xVar=0 := by simp [e,xVar,Polynomial.constantCoeff]
  have hv : e vVar=X := by simp [e,vVar,Polynomial.constantCoeff]
  have hw : e wVar=C X := by simp [e,wVar,Polynomial.constantCoeff]
  have hl (c : R) : e (lift4 c)=C (C c) := by simp [e,lift4,Polynomial.constantCoeff]
  change ((e (lift4 A*uVar*vVar^2*wVar^2+
    lift4 B*xVar*vVar^3*wVar+lift4 C₀*vVar^3*wVar^2)).coeff 3).coeff 2=C₀
  simp only [map_add,map_mul,map_pow,hu,hx,hv,hw,hl,zero_mul,mul_zero,zero_add]
  rw [← map_pow,mul_right_comm,← map_mul]
  norm_num only [Polynomial.coeff_C_mul_X_pow]
  simp only [ite_true,Polynomial.coeff_C_mul_X_pow]

def shiftedModel (a b τ σ : R) : Polynomial (Polynomial (Polynomial (P4 R))) :=
  leafModel (lift4 a) (lift4 b) (uVar+lift4 τ*vVar) vVar
    (xVar+lift4 σ*wVar) wVar

theorem exact_source_anchors (a b τ σ : R) :
    projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 2).coeff 1) = 1 ∧
    projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 1).coeff 1) = -2*τ ∧
    projectiveAnchor ((((shiftedModel a b τ σ).coeff 2).coeff 2).coeff 0) = τ+σ := by
  have h := shifted_leaf_anchors (lift4 a) (lift4 b) uVar xVar vVar wVar
    (lift4 τ) (lift4 σ)
  simp only [shiftedModel,h.1,h.2.1,h.2.2]
  refine ⟨?_,?_,?_⟩
  · simpa [lift4] using projective_anchor (0 : R) 0 1
  · simpa [lift4,mul_assoc,Polynomial.C_ofNat] using projective_anchor (-2 : R) 0 (-2*τ)
  · simpa [lift4] using projective_anchor (1 : R) 1 (τ+σ)

theorem exceptional_raw_zero (b x y w V T W : R) :
    primitive (-(x^2+x*y+y^2)) b x y w (-(x+y)*V) V T W = 0 := by
  have hs : firstSum x y (-(x+y)*V) V = 0 := by
    unfold firstSum
    ring
  have hf : first (-(x^2+x*y+y^2)) b x y (-(x+y)*V) V = 0 := by
    unfold first
    ring
  unfold primitive
  rw [hf,hs]
  simp

variable {K : Type*} [Field K]

theorem recover_two_parameters (scalar τ σ c d : K) (hscalar : scalar ≠ 0)
    (h₂ : (2 : K) ≠ 0) (hc : c=scalar*(-2*τ)) (hd : d=scalar*(τ+σ)) :
    τ=-c/(2*scalar) ∧ σ=d/scalar-τ := by
  constructor
  · apply (eq_div_iff (mul_ne_zero h₂ hscalar)).2
    rw [hc]
    ring
  · apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff hscalar).2
    rw [hd]
    ring

theorem exceptional_s3_square (a b x y : K) :
    CryptoLean.Semaev.S3 a b x y (-(x+y)) = (a+x^2+x*y+y^2)^2 := by
  unfold CryptoLean.Semaev.S3
  ring

theorem exceptional_s3_iff (a b x y : K) :
    CryptoLean.Semaev.S3 a b x y (-(x+y))=0 ↔ a=-(x^2+x*y+y^2) := by
  rw [exceptional_s3_square,pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)]
  constructor
  · intro h
    linear_combination h
  · intro h
    rw [h]
    ring

end CryptoLean.TwoChartCoefficients
