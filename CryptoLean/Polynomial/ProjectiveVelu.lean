import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring

/-! Homogeneous degree-two Vélu steps over semantic commutative rings. -/
namespace CryptoLean.Polynomial

/-- Numerator/denominator coordinates for `x ↦ x + tau / (x - xi)`.
The input and output are ordinary pairs in the coefficient ring. -/
def veluProjectiveStep {R : Type*} [CommRing R] (xi tau : R) (z : R × R) : R × R :=
  (z.1^2-xi*z.1*z.2+tau*z.2^2, z.1*z.2-xi*z.2^2)

/-- A unit Vélu parameter prevents a base point in the projective step.
This applies in quotient rings as well as fields, without inverse witnesses. -/
theorem isCoprime_veluProjectiveStep {R : Type*} [CommRing R]
    {A B xi tau : R} (h : IsCoprime A B) (ht : IsUnit tau) :
    IsCoprime (veluProjectiveStep xi tau (A,B)).1
      (veluProjectiveStep xi tau (A,B)).2 := by
  change IsCoprime (A^2-xi*A*B+tau*B^2) (A*B-xi*B^2)
  have hNB : IsCoprime (A^2-xi*A*B+tau*B^2) B := by
    convert (h.pow_left : IsCoprime (A^2) B).add_mul_right_left (-xi*A+tau*B) using 1
    ring
  have hBq : IsCoprime B (A-xi*B) :=
    IsCoprime.sub_mul_right_right_iff.mpr h.symm
  have htq : IsCoprime tau (A-xi*B) :=
    isCoprime_one_left.of_isCoprime_of_dvd_left ht.dvd
  have hNq : IsCoprime (A^2-xi*A*B+tau*B^2) (A-xi*B) := by
    convert (htq.mul_left (hBq.pow_left : IsCoprime (B^2) (A-xi*B))).add_mul_right_left A using 1
    ring
  convert hNB.mul_right hNq using 1
  ring

end CryptoLean.Polynomial
