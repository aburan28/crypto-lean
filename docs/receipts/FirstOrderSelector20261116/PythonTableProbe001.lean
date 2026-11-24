import CryptoLean.Polynomial.EndpointCoefficients
set_option autoImplicit false
noncomputable section
namespace PythonTableProbe001
variable {R : Type*} [CommRing R]
def sourceVector (a b τ : R) : Fin 20 → R := ![
  1,
  (-2),
  1,
  (2*τ),
  ((-4)*τ),
  (2*τ),
  (-2),
  (-2),
  ((-2)*a),
  ((-2)*a),
  ((-4)*b),
  (τ*τ),
  ((((-2)*τ)*τ)-(2*a)),
  (τ*τ),
  ((-2)*τ),
  ((-2)*τ),
  ((((-2)*a)*τ)-(4*b)),
  ((((-2)*a)*τ)-(4*b)),
  ((a*a)-((4*b)*τ)),
  1]
theorem sourceVector_eq_model (a b τ : R) :
    sourceVector a b τ = CryptoLean.EndpointCoefficients.firstVector a b τ := by
  funext i
  fin_cases i <;> norm_num [sourceVector,CryptoLean.EndpointCoefficients.firstVector]
  all_goals ring
#print axioms sourceVector_eq_model
end PythonTableProbe001
