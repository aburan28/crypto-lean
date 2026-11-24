module
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Scalar-two retractions from pair-incidence correspondences

This is an additive homomorphism law over inherited Mathlib structures.
It does not construct geometric correspondences or identify Jacobians.
-/
set_option autoImplicit false

public section

namespace CryptoLean.PairIncidenceModule

variable {A B D E : Type*} [AddMonoid A] [AddMonoid B]
  [AddMonoid D] [AddMonoid E]

/-- A split input in the norm kernel gives a scalar-two retraction when
the correspondence Gram identity is twice the identity plus pull-norm. -/
theorem scalar_two_retraction
    (input : A →+ B) (retract : B →+ A)
    (transfer : B →+ D) (adjoint : D →+ B)
    (norm : B →+ E) (pull : E →+ B)
    (hleft : ∀ a : A, retract (input a) = a)
    (hkernel : ∀ a : A, norm (input a) = 0)
    (hgram : ∀ b : B, adjoint (transfer b) = b + b + pull (norm b))
    (a : A) : retract (adjoint (transfer (input a))) = a + a := by
  calc
    retract (adjoint (transfer (input a))) = retract (input a + input a) := by
      rw [hgram, hkernel, map_zero, add_zero]
    _ = a + a := by rw [map_add, hleft, hleft]

/-- The chained transfer is injective on any actual additive domain on
which doubling is injective. No torsion or geometric hypothesis is hidden. -/
theorem chain_injective_of_double_injective
    (input : A →+ B) (retract : B →+ A)
    (transfer : B →+ D) (adjoint : D →+ B)
    (norm : B →+ E) (pull : E →+ B)
    (hleft : ∀ a : A, retract (input a) = a)
    (hkernel : ∀ a : A, norm (input a) = 0)
    (hgram : ∀ b : B, adjoint (transfer b) = b + b + pull (norm b))
    (hdouble : Function.Injective (fun a : A => a + a)) :
    Function.Injective (fun a : A => transfer (input a)) := by
  intro a b hab
  apply hdouble
  calc
    a + a = retract (adjoint (transfer (input a))) :=
      (scalar_two_retraction input retract transfer adjoint norm pull
        hleft hkernel hgram a).symm
    _ = retract (adjoint (transfer (input b))) :=
      congrArg (fun d : D => retract (adjoint d)) hab
    _ = b + b := scalar_two_retraction input retract transfer adjoint norm pull
      hleft hkernel hgram b

end CryptoLean.PairIncidenceModule

#print axioms CryptoLean.PairIncidenceModule.scalar_two_retraction
#print axioms CryptoLean.PairIncidenceModule.chain_injective_of_double_injective
