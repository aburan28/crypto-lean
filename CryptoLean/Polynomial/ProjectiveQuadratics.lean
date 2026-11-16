import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-! An explicit one-vertex projective elimination witness. The witness is
useful before saturation; no growing-system solver is asserted. -/
set_option autoImplicit false

namespace CryptoLean.ProjectiveQuadratics

variable {R : Type*} [CommRing R]

theorem bezout_identity (a b c d e f U V : R) :
    ((a*f-c*d)^2-(a*e-b*d)*(b*f-c*e))*V^3 =
      (a*((a*f-c*d)*V-(a*e-b*d)*U)-(a*e-b*d)*b*V)*
        (d*U^2+e*U*V+f*V^2) +
      (-d*((a*f-c*d)*V-(a*e-b*d)*U)+(a*e-b*d)*e*V)*
        (a*U^2+b*U*V+c*V^2) := by ring

theorem ideal_witness (I : Ideal R) (a b c d e f U V : R)
    (hF : a*U^2+b*U*V+c*V^2 ∈ I) (hG : d*U^2+e*U*V+f*V^2 ∈ I) :
    ((a*f-c*d)^2-(a*e-b*d)*(b*f-c*e))*V^3 ∈ I := by
  rw [bezout_identity]
  exact I.add_mem (I.mul_mem_left _ hG) (I.mul_mem_left _ hF)

theorem common_root [IsDomain R] (a b c d e f U V : R) (hV : V ≠ 0)
    (hF : a*U^2+b*U*V+c*V^2 = 0) (hG : d*U^2+e*U*V+f*V^2 = 0) :
    (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e) = 0 := by
  have h := bezout_identity a b c d e f U V
  rw [hF, hG, mul_zero, mul_zero, add_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hV)

end CryptoLean.ProjectiveQuadratics
