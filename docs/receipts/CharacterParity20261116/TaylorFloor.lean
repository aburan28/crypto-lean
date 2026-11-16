import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Polynomial

example {R : Type*} [CommRing R] (a : R) (m : ℕ) (g : R[X]) :
    (taylor a ((X-C a)^m*g)).coeff m = g.eval a := by
  have hs : taylor a (X-C a) = (X : R[X]) := by simp [taylor_apply]
  rw [taylor_mul, taylor_pow, hs]
  simpa using (coeff_X_pow_mul (taylor a g) m 0)

example (p : ℕ) [Fact p.Prime] (a : ZMod p) (m : ℕ) (g : (ZMod p)[X]) :
    (taylor a ((X-C a)^m*g)).coeff m = g.eval a := by
  have hs : taylor a (X-C a) = (X : (ZMod p)[X]) := by simp [taylor_apply]
  rw [taylor_mul, taylor_pow, hs]
  simpa using (coeff_X_pow_mul (taylor a g) m 0)
