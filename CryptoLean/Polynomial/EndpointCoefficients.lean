import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! Actual endpoint S3 coefficients, checked as nested univariate polynomials.
No elliptic-curve group or small-root existence claim. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.EndpointCoefficients
open Polynomial
open scoped BigOperators
variable {R : Type*} [CommRing R]

def endpointInX (a b y U V τ : R) : Polynomial R :=
  (X-C y)^2*C (U+τ*V)^2 -
    2*((X+C y)*(X*C y+C a)+2*C b)*C (U+τ*V)*C V +
    ((X*C y-C a)^2-4*C b*(X+C y))*C V^2

theorem endpoint_expansion (a b y U V τ : R) :
    endpointInX a b y U V τ =
      C ((U+(τ-y)*V)^2)*X^2 +
      C (-2*y*(U+τ*V)^2-2*(y^2+a)*(U+τ*V)*V-(2*a*y+4*b)*V^2)*X +
      C (y^2*(U+τ*V)^2-2*(a*y+2*b)*(U+τ*V)*V+(a^2-4*b*y)*V^2) := by
  simp only [endpointInX, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
  ring

theorem endpoint_x_square (a b y U V τ : R) :
    (endpointInX a b y U V τ).coeff 2 = (U+(τ-y)*V)^2 := by
  rw [endpoint_expansion]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

theorem translated_y_square_coeffs (U V τ : R) :
    ((C U+(C τ-X)*C V)^2 : Polynomial R).coeff 2 = V^2 ∧
    ((C U+(C τ-X)*C V)^2 : Polynomial R).coeff 0 = (U+τ*V)^2 := by
  have h : ((C U+(C τ-X)*C V)^2 : Polynomial R) =
      C (V^2)*X^2+C (-2*V*(U+τ*V))*X+C ((U+τ*V)^2) := by
    simp only [map_add, map_mul, map_pow, map_neg, map_ofNat]
    ring
  rw [h]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

theorem translated_u_square_coeffs (V τ : R) :
    ((X+C τ*C V)^2 : Polynomial R).coeff 2 = 1 ∧
    ((X+C τ*C V)^2 : Polynomial R).coeff 1 = 2*τ*V := by
  have h : ((X+C τ*C V)^2 : Polynomial R) =
      X^2+C (2*τ*V)*X+C ((τ*V)^2) := by
    simp only [map_mul, map_pow, map_ofNat]
    ring
  rw [h]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
  norm_num

variable {K : Type*} [CommRing K]

abbrev VPoly (K : Type*) [CommRing K] := Polynomial K
abbrev UVPoly (K : Type*) [CommRing K] := Polynomial (VPoly K)
abbrev YUVPoly (K : Type*) [CommRing K] := Polynomial (UVPoly K)

def firstEndpoint (a b τ : K) : Polynomial (YUVPoly K) :=
  endpointInX (C (C (C a))) (C (C (C b))) X
    (C X) (C (C X)) (C (C (C τ)))

/-- The coefficient of x² y² U⁰ V² is one. -/
theorem first_endpoint_coefficient_one (a b τ : K) :
    (((((firstEndpoint a b τ).coeff 2).coeff 2).coeff 0).coeff 2) = 1 := by
  rw [firstEndpoint, endpoint_x_square]
  rw [(translated_y_square_coeffs (X : UVPoly K) (C X) (C (C τ))).1]
  rw [← map_pow, Polynomial.coeff_C_zero]
  simp

/-- The coefficient of x² y⁰ U¹ V¹ is twice the offset. -/
theorem first_endpoint_coefficient_offset (a b τ : K) :
    (((((firstEndpoint a b τ).coeff 2).coeff 0).coeff 1).coeff 1) = 2*τ := by
  rw [firstEndpoint, endpoint_x_square]
  rw [(translated_y_square_coeffs (X : UVPoly K) (C X) (C (C τ))).2]
  rw [(translated_u_square_coeffs (X : VPoly K) (C τ)).2]
  simp

def lastEndpoint (a b q τ : K) : Polynomial (UVPoly K) :=
  endpointInX (C (C a)) (C (C b)) (C (C q)) X (C X) (C (C τ))

/-- The coefficient of x² U² V⁰ at the last endpoint is one. -/
theorem last_endpoint_coefficient_one (a b q τ : K) :
    ((((lastEndpoint a b q τ).coeff 2).coeff 2).coeff 0) = 1 := by
  rw [lastEndpoint, endpoint_x_square]
  have h := (translated_u_square_coeffs (X : VPoly K) (C τ-C q)).1
  simp only [map_sub] at h
  rw [h]
  simp

/-- The coefficient of x² U¹ V¹ at the last endpoint is twice tau-q. -/
theorem last_endpoint_coefficient_offset (a b q τ : K) :
    ((((lastEndpoint a b q τ).coeff 2).coeff 1).coeff 1) = 2*(τ-q) := by
  rw [lastEndpoint, endpoint_x_square]
  have h := (translated_u_square_coeffs (X : VPoly K) (C τ-C q)).2
  simp only [map_sub] at h
  rw [h]
  simp

def firstExponents : Fin 20 → Fin 4 → ℕ := ![
  ![2,0,2,0], ![1,1,2,0], ![0,2,2,0], ![2,0,1,1], ![1,1,1,1],
  ![0,2,1,1], ![2,1,1,1], ![1,2,1,1], ![1,0,1,1], ![0,1,1,1],
  ![0,0,1,1], ![2,0,0,2], ![1,1,0,2], ![0,2,0,2], ![2,1,0,2],
  ![1,2,0,2], ![1,0,0,2], ![0,1,0,2], ![0,0,0,2], ![2,2,0,2]]

theorem first_exponents_injective : Function.Injective firstExponents := by decide

def firstVector (a b τ : R) : Fin 20 → R := ![
  1,-2,1,2*τ,-4*τ,2*τ,-2,-2,-2*a,-2*a,-4*b,
  τ^2,-2*τ^2-2*a,τ^2,-2*τ,-2*τ,-2*a*τ-4*b,-2*a*τ-4*b,a^2-4*b*τ,1]

def firstMonomials (x y U V : R) (i : Fin 20) : R :=
  x^(firstExponents i 0)*y^(firstExponents i 1)*
    U^(firstExponents i 2)*V^(firstExponents i 3)

def firstWeights (B H : ℕ) (i : Fin 20) : ℕ :=
  B^(firstExponents i 0+firstExponents i 1)*H^(firstExponents i 2+firstExponents i 3)

theorem first_vector_expansion (a b τ x y U V : R) :
    ∑ i, firstVector a b τ i*firstMonomials x y U V i =
      (x-y)^2*(U+τ*V)^2 - 2*((x+y)*(x*y+a)+2*b)*(U+τ*V)*V +
        ((x*y-a)^2-4*b*(x+y))*V^2 := by
  norm_num [firstVector,firstMonomials,firstExponents,Fin.sum_univ_succ]
  ring

theorem integer_monomial_bound (B H i j k l : ℕ) (x y U V : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hU : U.natAbs ≤ H) (hV : V.natAbs ≤ H) :
    (x^i*y^j*U^k*V^l).natAbs ≤ B^(i+j)*H^(k+l) := by
  simp only [Int.natAbs_mul,Int.natAbs_pow]
  calc
    _ ≤ B^i*B^j*H^k*H^l := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hx i)
        (Nat.pow_le_pow_left hy j)) (Nat.pow_le_pow_left hU k))
      (Nat.pow_le_pow_left hV l)
    _ = _ := by rw [pow_add,pow_add]; ring

theorem first_monomials_bound (B H : ℕ) (x y U V : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hU : U.natAbs ≤ H) (hV : V.natAbs ≤ H) (i : Fin 20) :
    (firstMonomials x y U V i).natAbs ≤ firstWeights B H i :=
  integer_monomial_bound B H _ _ _ _ x y U V hx hy hU hV

end CryptoLean.EndpointCoefficients
