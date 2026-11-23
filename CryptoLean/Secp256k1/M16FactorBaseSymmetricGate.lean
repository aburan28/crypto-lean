import Mathlib
import CryptoLean.Secp256k1.M16FactorBaseFinite
import CryptoLean.Secp256k1.M16SolverGate

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/M16FactorBaseSymmetricGate.lean at 0a47cd62f43d (PR #347).
/-!
# Exact unordered tuple counts for the M16 factor base

`Sym FactorBaseX k` is the type of size-`k` multisets, so it retains repeated
x-coordinates while quotienting only by permutation.  Stars-and-bars gives its
exact cardinality.  At the desk ceiling recorded by `M16SolverGate`, width six
fits and width seven does not.

These are representation counts only.  They do not show that the coordinates
lift to curve points, that a target relation exists, or that any solver runs
within the stated ceiling.
-/

namespace CryptoLean.Secp256k1.M16FactorBaseSymmetricGate

open CryptoLean.Secp256k1.M16FactorBaseFinite
open CryptoLean.Secp256k1.M16SolverGate

/-- Exact number of size-six multisets from the full root-based factor base. -/
theorem card_sym_factorBaseX_six :
    Fintype.card (Sym FactorBaseX 6) =
      44953578811715702293911690083685 := by
  rw [Sym.card_sym_eq_choose, card_factorBaseX]
  norm_num [Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]

/-- The size-six multiset representation fits below the desk ceiling. -/
theorem card_sym_factorBaseX_six_le_budget :
    Fintype.card (Sym FactorBaseX 6) ≤ maxRelationTermBudget := by
  rw [card_sym_factorBaseX_six]
  norm_num [maxRelationTermBudget]

/-- Exact number of size-seven multisets from the full root-based factor base. -/
theorem card_sym_factorBaseX_seven :
    Fintype.card (Sym FactorBaseX 7) =
      3625364848488605997796768368508932240 := by
  rw [Sym.card_sym_eq_choose, card_factorBaseX]
  norm_num [Nat.choose_eq_descFactorial_div_factorial,
    Nat.descFactorial, Nat.factorial]

/-- The desk ceiling is strictly below the size-seven multiset count. -/
theorem budget_lt_card_sym_factorBaseX_seven :
    maxRelationTermBudget < Fintype.card (Sym FactorBaseX 7) := by
  rw [card_sym_factorBaseX_seven]
  norm_num [maxRelationTermBudget]

end CryptoLean.Secp256k1.M16FactorBaseSymmetricGate
