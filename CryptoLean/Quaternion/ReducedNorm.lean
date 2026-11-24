import Mathlib.Algebra.Quaternion

/-!
# The reduced norm of a quaternion algebra, as a monoid homomorphism

Mathlib bundles the norm of *Hamilton* quaternions (`Quaternion.normSq : ℍ[R] →*₀ R`) and,
for a general quaternion algebra `ℍ[R, c₁, c₂, c₃]`, proves that `a * star a` is a scalar
(`QuaternionAlgebra.mul_star_eq_coe`). The reduced norm `nrd a = (a * star a).re` of a
general algebra, as a multiplicative map, is the missing component built here
(an upstream candidate for Mathlib). SQIsign uses it for
`B_{p,∞} = ℍ[ℚ, -1, 0, -p]`, where the degree of an isogeny is the reduced norm of the
corresponding ideal element (the Deuring dictionary).
-/

set_option autoImplicit false

open scoped Quaternion

namespace CryptoLean.Deuring

variable {R : Type*} [CommRing R] {c₁ c₂ c₃ : R}

/-- The reduced norm `nrd a = (a * star a).re`. -/
def nrd (a : ℍ[R,c₁,c₂,c₃]) : R := (a * star a).re

theorem mul_star_eq_nrd (a : ℍ[R,c₁,c₂,c₃]) : a * star a = ((nrd a : R) : ℍ[R,c₁,c₂,c₃]) :=
  QuaternionAlgebra.mul_star_eq_coe a

/-- **The reduced norm is multiplicative.** `a b * star (a b) = a (b * star b) star a`
and `b * star b` is central. -/
theorem nrd_mul (a b : ℍ[R,c₁,c₂,c₃]) : nrd (a * b) = nrd a * nrd b := by
  have h : (a * b) * star (a * b) = ((nrd a * nrd b : R) : ℍ[R,c₁,c₂,c₃]) := by
    rw [star_mul, mul_assoc, ← mul_assoc b, mul_star_eq_nrd b,
      QuaternionAlgebra.coe_commutes (nrd b) (star a), ← mul_assoc, mul_star_eq_nrd a,
      ← QuaternionAlgebra.coe_mul]
  show ((a * b) * star (a * b)).re = _
  rw [h, QuaternionAlgebra.re_coe]

theorem nrd_one : nrd (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by
  simp [nrd]

/-- The reduced norm as a `MonoidHom`. -/
def nrdHom : ℍ[R,c₁,c₂,c₃] →* R where
  toFun := nrd
  map_one' := nrd_one
  map_mul' := nrd_mul

/-- For `c₂ = 0` (`i² = c₁`, `j² = c₃`): `nrd a = re² - c₁ imI² - c₃ imJ² + c₁ c₃ imK²`. -/
theorem nrd_eq (a : ℍ[R,c₁,0,c₃]) :
    nrd a = a.re ^ 2 - c₁ * a.imI ^ 2 - c₃ * a.imJ ^ 2 + c₁ * c₃ * a.imK ^ 2 := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-- The reduced trace `trd a = a + star a` is a scalar when `c₂ = 0`: `trd a = 2 re a`. -/
theorem add_star_eq (a : ℍ[R,c₁,0,c₃]) :
    a + star a = ((a.re + a.re : R) : ℍ[R,c₁,0,c₃]) := by
  ext <;> simp

end CryptoLean.Deuring
