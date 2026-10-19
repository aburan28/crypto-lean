import CryptoLean.Group.CyclicEncoding
import CryptoLean.Group.CoprimeTransport
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace CryptoLean.Controls
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- An annihilation relation alone cannot certify an injective encoding. -/
theorem annihilation_without_exact_order_not_injective :
    ¬ Function.Injective (Cyclic.encode (n := 7) (0 : ZMod 7) (by simp)) := by
  intro h
  have hz : (0 : ZMod 7) = 1 := h (by rw [Cyclic.encode_val, Cyclic.encode_val]; simp)
  exact (by decide : (0 : ZMod 7) ≠ 1) hz

/-- A nonzero denominator in a composite scalar ring can annihilate x. -/
theorem composite_collision :
    (0 : ZMod 6) + 2 * 3 = 0 + 0 * 3 ∧ (2 : ZMod 6) ≠ 0 ∧ (3 : ZMod 6) ≠ 0 := by
  decide

/-- Without a nonzero denominator, an ordinary collision gives no recovery. -/
theorem zero_denominator_collision :
    (0 : ZMod 7) + 0 * 1 = 0 + 0 * 1 ∧ (1 : ZMod 7) ≠ ((0 : ZMod 7) - 0) / ((0 : ZMod 7) - 0) := by
  norm_num

/-- The negation collision also needs its own sum-denominator condition. -/
theorem zero_sum_denominator_collision :
    (0 : ZMod 7) + 0 * 1 = -(0 + 0 * 1) ∧ (1 : ZMod 7) ≠ -((0 : ZMod 7) + 0) / ((0 : ZMod 7) + 0) := by
  norm_num

/-- Noncoprime multiplication can lose a nonzero subgroup point. -/
theorem noncoprime_transport_loses_point :
    (2 : ℕ) • (3 : ZMod 6) = 0 ∧ (3 : ZMod 6) ≠ 0 := by decide
end CryptoLean.Controls
