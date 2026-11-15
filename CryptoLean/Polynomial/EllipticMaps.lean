import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Algebraic identities behind finite-point halving and the rational degree-two
Vélu formula (MIT18.783 Fall2023, Lecture2 section2.2 and Lecture5 Theorem5.13).
These are identities on semantic rings/fields, not a proof of a native program,
the elliptic group law, rational-root completeness, or an isogeny constructor. -/

set_option autoImplicit false

namespace CryptoLean.Polynomial

variable {R : Type*} [CommRing R]

def doublingQuartic (a b xp x : R) : R :=
  x^4 - 4*xp*x^3 - 2*a*x^2 - (8*b + 4*a*xp)*x + a^2 - 4*b*xp

/-- Clearing the affine doubling-abscissa equation gives this quartic.
Nonzero denominator, ordinate, and point/group interpretation are separate. -/
theorem cleared_doubling_quartic (a b xp x : R) :
    (3*x^2+a)^2 - 4*(2*x+xp)*(x^3+a*x+b) = doublingQuartic a b xp x := by
  dsimp [doublingQuartic]
  ring

def veluTau (a xi : R) : R := 3*xi^2+a
def veluNumerator (a xi x : R) : R := x^2-xi*x+veluTau a xi
def veluCodomainA (a xi : R) : R := a-5*veluTau a xi
def veluCodomainB (a b xi : R) : R := b-7*xi*veluTau a xi

/-- The exact residual before imposing that `(xi,0)` is on the curve. -/
theorem velu_two_curve_residual (a b xi x : R) :
    (x^3+a*x+b)*((x-xi)^2-veluTau a xi)^2 -
      ((veluNumerator a xi x)^3*(x-xi) +
       veluCodomainA a xi*veluNumerator a xi x*(x-xi)^3 +
       veluCodomainB a b xi*(x-xi)^4) =
    (xi^3+a*xi+b)*veluTau a xi*(veluTau a xi-2*(x-xi)^2) := by
  dsimp [veluTau, veluNumerator, veluCodomainA, veluCodomainB]
  ring

/-- A kernel abscissa on the source curve makes the cleared equation exact. -/
theorem velu_two_curve_identity (a b xi x : R) (hroot : xi^3+a*xi+b=0) :
    (x^3+a*x+b)*((x-xi)^2-veluTau a xi)^2 =
      (veluNumerator a xi x)^3*(x-xi) +
       veluCodomainA a xi*veluNumerator a xi x*(x-xi)^3 +
       veluCodomainB a b xi*(x-xi)^4 := by
  apply sub_eq_zero.mp
  simpa only [hroot, zero_mul] using velu_two_curve_residual a b xi x

/-- The actual affine rational coordinates satisfy the codomain equation.
This assumes a nonzero denominator; it asserts no value at a pole and does not
construct a morphism or prove its homomorphism/degree/subgroup properties. -/
theorem velu_two_affine_curve {K : Type*} [Field K]
    (a b xi x y : K) (hroot : xi^3+a*xi+b=0)
    (hpoint : y^2=x^3+a*x+b) (hden : x-xi≠0) :
    (y*((x-xi)^2-veluTau a xi)/(x-xi)^2)^2 =
      (veluNumerator a xi x/(x-xi))^3 +
       veluCodomainA a xi*(veluNumerator a xi x/(x-xi)) +
       veluCodomainB a b xi := by
  have hclear := velu_two_curve_identity a b xi x hroot
  rw [← hpoint] at hclear
  field_simp [hden]
  linear_combination hclear

end CryptoLean.Polynomial
