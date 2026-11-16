import CryptoLean.Polynomial.EndpointCoefficients

/-! Degree-at-most-one leaf multiplier pivots for the actual S3 endpoint.
These identities do not establish general triangular search or useful yield. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.MixedDegreePivots
open Polynomial CryptoLean.EndpointCoefficients
variable {R : Type*} [CommRing R]

def v2InX (a b y τ : R) : Polynomial R :=
  C ((τ-y)^2)*X^2 +
  C (-2*y*τ^2-2*(y^2+a)*τ-(2*a*y+4*b))*X +
  C (y^2*τ^2-2*(a*y+2*b)*τ+(a^2-4*b*y))

def uvInX (a b y τ : R) : Polynomial R :=
  C (2*τ-2*y)*X^2 + C (-4*τ*y-2*y^2-2*a)*X +
  C (2*τ*y^2-2*a*y-4*b)

theorem v2_as_endpoint (a b y τ : R) :
    v2InX a b y τ = endpointInX a b y 0 1 τ := by
  rw [endpoint_expansion]
  simp [v2InX]

theorem endpoint_coefficient_split (a b y U V τ : R) :
    endpointInX a b y U V τ =
      C (U^2)*(X-C y)^2+C (U*V)*uvInX a b y τ+C (V^2)*v2InX a b y τ := by
  simp only [endpointInX,uvInX,v2InX,map_add,map_sub,map_mul,map_pow,map_neg,map_ofNat]
  ring

theorem linear_quadratic_coeffs (A D q₂ q₁ q₀ : R) :
    ((C A*X+C D)*(C q₂*X^2+C q₁*X+C q₀)).coeff 3 = A*q₂ ∧
    ((C A*X+C D)*(C q₂*X^2+C q₁*X+C q₀)).coeff 2 = A*q₁+D*q₂ := by
  have h : (C A*X+C D)*(C q₂*X^2+C q₁*X+C q₀) =
      C (A*q₂)*X^3+C (A*q₁+D*q₂)*X^2+C (A*q₀+D*q₁)*X+C (D*q₀) := by
    simp only [map_add,map_mul]
    ring
  rw [h]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

def multiplier (A B L τ : R) : Polynomial (Polynomial R) :=
  C (C A)*X+C (C B*X+C (L+2*τ*(A+B)))

def mixedV2 (a b τ A B L : R) : Polynomial (Polynomial R) :=
  multiplier A B L τ * v2InX (C a) (C b) X (C τ)

def mixedUV (a b τ A B L : R) : Polynomial (Polynomial R) :=
  multiplier A B L τ * uvInX (C a) (C b) X (C τ)

theorem mixed_v2_pivots (a b τ A B L : R) :
    ((mixedV2 a b τ A B L).coeff 3).coeff 2 = A ∧
    ((mixedV2 a b τ A B L).coeff 2).coeff 3 = B ∧
    ((mixedV2 a b τ A B L).coeff 2).coeff 2 = L := by
  have h := linear_quadratic_coeffs (C A)
    (C B*X+C (L+2*τ*(A+B))) ((C τ-X)^2)
    (-2*X*(C τ)^2-2*(X^2+C a)*C τ-(2*C a*X+4*C b))
    (X^2*(C τ)^2-2*(C a*X+2*C b)*C τ+((C a)^2-4*C b*X))
  simp only [mixedV2,multiplier,v2InX,h.1,h.2]
  have h₃ : C A*(C τ-X)^2 = C A*X^2+C (-2*A*τ)*X+C (A*τ^2) := by
    simp only [map_neg,map_mul,map_pow,map_ofNat]
    ring
  have h₂ :
      C A*(-2*X*(C τ)^2-2*(X^2+C a)*C τ-(2*C a*X+4*C b)) +
        (C B*X+C (L+2*τ*(A+B)))*(C τ-X)^2 =
      C B*X^3+C L*X^2 +
        C (-2*A*τ^2-2*a*A+B*τ^2-2*(L+2*τ*(A+B))*τ)*X +
        C (-2*a*A*τ-4*b*A+(L+2*τ*(A+B))*τ^2) := by
    simp only [map_add,map_sub,map_neg,map_mul,map_pow,map_ofNat]
    ring
  rw [h₃,h₂]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

theorem mixed_uv_anchors (a b τ A B L : R) :
    ((mixedUV a b τ A B L).coeff 3).coeff 0 = 2*A*τ ∧
    ((mixedUV a b τ A B L).coeff 2).coeff 1 = -8*A*τ-2*B*τ-2*L ∧
    ((mixedUV a b τ A B L).coeff 2).coeff 0 =
      2*τ*(L+2*τ*(A+B))-2*a*A := by
  have h := linear_quadratic_coeffs (C A)
    (C B*X+C (L+2*τ*(A+B))) (2*C τ-2*X)
    (-4*C τ*X-2*X^2-2*C a) (2*C τ*X^2-2*C a*X-4*C b)
  simp only [mixedUV,multiplier,uvInX,h.1,h.2]
  have h₃ : C A*(2*C τ-2*X) = C (-2*A)*X+C (2*A*τ) := by
    simp only [map_neg,map_mul,map_ofNat]
    ring
  have h₂ :
      C A*(-4*C τ*X-2*X^2-2*C a) +
        (C B*X+C (L+2*τ*(A+B)))*(2*C τ-2*X) =
      C (-2*A-2*B)*X^2+C (-8*A*τ-2*B*τ-2*L)*X +
        C (2*τ*(L+2*τ*(A+B))-2*a*A) := by
    simp only [map_add,map_sub,map_neg,map_mul,map_ofNat]
    ring
  rw [h₃,h₂]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

theorem mixed_anchor_branch_y (a b τ B L : R) :
    ((mixedUV a b τ 0 B L).coeff 2).coeff 1 = -2*B*τ-2*L := by
  simpa using (mixed_uv_anchors a b τ 0 B L).2.1

theorem mixed_anchor_branch_constant (a b τ L : R) :
    ((mixedUV a b τ 0 0 L).coeff 2).coeff 0 = 2*L*τ := by
  rw [(mixed_uv_anchors a b τ 0 0 L).2.2]
  ring

end CryptoLean.MixedDegreePivots
