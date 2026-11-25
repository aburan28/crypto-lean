import CryptoLean.Quaternion.MaximalOrderO0
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# `B_{p,∞}` is a division algebra

SQIsign's key space, its ideal classes and its "equivalent ideal" step
(`J = I · ᾱ / nrd(I)` for `α ∈ I`) all divide by elements of `B_{p,∞}`. This needs every
nonzero element to be invertible, i.e. that `B_{p,∞} = (-1, -p | ℚ)` is a *division*
quaternion algebra (it is ramified at `∞`). Here, for `p = 4m + 3`:

* `nrd_bp`: `nrd(a + b i + c j + d k) = a² + b² + p (c² + d²)` (diagonal positive form);
* `nrd_bp_pos`: the reduced norm is positive on nonzero elements (definite at `∞`);
* `bp_unit`: every nonzero `x` is a unit, with inverse `x̄ / nrd x`;
* `bp_mul_inv` / `bp_inv_mul`: the two inverse identities.

Inheritance (lean-instance-gate): `QuaternionAlgebra.mul_star_eq_coe` and
`QuaternionAlgebra.star_mul_eq_coe` from Mathlib, `nrd_eq` from `ReducedNorm.lean`.
-/

set_option autoImplicit false

open scoped Quaternion

namespace CryptoLean.Deuring

/-- Diagonal norm form of `B_{p,∞}`. -/
theorem nrd_bp (m : ℕ) (x : Bp m) :
    nrd x = x.re ^ 2 + x.imI ^ 2 + (4 * (m : ℚ) + 3) * (x.imJ ^ 2 + x.imK ^ 2) := by
  rw [nrd_eq]
  ring

/-- **`B_{p,∞}` is definite.** The reduced norm of a nonzero element is positive. -/
theorem nrd_bp_pos (m : ℕ) {x : Bp m} (hx : x ≠ 0) : 0 < nrd x := by
  rw [nrd_bp]
  have hp : (0 : ℚ) < 4 * m + 3 := by positivity
  have h0 : 0 ≤ x.re ^ 2 := sq_nonneg _
  have h1 : 0 ≤ x.imI ^ 2 := sq_nonneg _
  have h2 : 0 ≤ x.imJ ^ 2 := sq_nonneg _
  have h3 : 0 ≤ x.imK ^ 2 := sq_nonneg _
  by_cases ha : x.re = 0
  · by_cases hb : x.imI = 0
    · by_cases hc : x.imJ = 0
      · have hd : x.imK ≠ 0 := fun hd => hx (QuaternionAlgebra.ext ha hb hc hd)
        have : 0 < x.imK ^ 2 := by positivity
        nlinarith
      · have : 0 < x.imJ ^ 2 := by positivity
        nlinarith
    · have : 0 < x.imI ^ 2 := by positivity
      nlinarith
  · have : 0 < x.re ^ 2 := by positivity
    nlinarith

/-- The inverse `x̄ / nrd x`. -/
def bpInv (m : ℕ) (x : Bp m) : Bp m := star x * (((nrd x)⁻¹ : ℚ) : Bp m)

theorem bp_mul_inv (m : ℕ) {x : Bp m} (hx : x ≠ 0) : x * bpInv m x = 1 := by
  have hn : nrd x ≠ 0 := (nrd_bp_pos m hx).ne'
  rw [bpInv, ← mul_assoc, mul_star_eq_nrd, ← QuaternionAlgebra.coe_mul, mul_inv_cancel₀ hn,
    QuaternionAlgebra.coe_one]

theorem bp_inv_mul (m : ℕ) {x : Bp m} (hx : x ≠ 0) : bpInv m x * x = 1 := by
  have hn : nrd x ≠ 0 := (nrd_bp_pos m hx).ne'
  have hs : star x * x = ((nrd x : ℚ) : Bp m) := by
    rw [QuaternionAlgebra.star_mul_eq_coe]
    congr 1
    show (star x * x).re = (x * star x).re
    simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star,
      QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
    ring
  rw [bpInv, mul_assoc, QuaternionAlgebra.coe_commutes, ← mul_assoc, hs,
    ← QuaternionAlgebra.coe_mul, mul_inv_cancel₀ hn, QuaternionAlgebra.coe_one]

/-- **Every nonzero element of `B_{p,∞}` is a unit.** -/
def bpUnit (m : ℕ) {x : Bp m} (hx : x ≠ 0) : (Bp m)ˣ :=
  ⟨x, bpInv m x, bp_mul_inv m hx, bp_inv_mul m hx⟩

theorem bp_isUnit (m : ℕ) {x : Bp m} (hx : x ≠ 0) : IsUnit x :=
  ⟨bpUnit m hx, rfl⟩

end CryptoLean.Deuring
