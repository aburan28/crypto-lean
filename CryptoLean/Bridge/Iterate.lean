import CryptoLeanCore.Iterate
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Bridge: `CryptoLeanCore.iterate` is Mathlib's `Nat.iterate`

A return-time fact proved in the Std-only layer transfers to Mathlib's
`f^[n]` and `Function.IsPeriodicPt`.
-/

namespace CryptoLean.Bridge

variable {α : Type*} (f : α → α)

theorem iterate_eq (n : ℕ) : CryptoLeanCore.iterate f n = f^[n] := by
  induction n with
  | zero => rfl
  | succ n ih => funext x; simp [CryptoLeanCore.iterate, ih, Function.iterate_succ_apply]

theorem returns_iff_isPeriodicPt (n : ℕ) (x : α) :
    CryptoLeanCore.Returns f n x ↔ Function.IsPeriodicPt f n x := by
  simp [CryptoLeanCore.Returns, Function.IsPeriodicPt, Function.IsFixedPt, iterate_eq]

end CryptoLean.Bridge
