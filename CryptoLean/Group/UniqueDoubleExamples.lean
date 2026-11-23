import CryptoLean.Group.UniqueDouble
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Prod

/-!
# Inherited product instances and hypothesis controls

All operations, groups, homomorphisms and equivalences are Mathlib instances.
The finite checks use kernel-reduced `decide`, with no native compiler axiom.
No equivalence with the earlier custom Bool carrier is asserted here.
-/
set_option autoImplicit false

namespace CryptoLean.UniqueDouble.Examples

abbrev Mixed := ZMod 4 × (ZMod 2 × ZMod 2)
def point : Mixed := (2, (0, 0))

theorem doubled_range : ∀ x : Mixed, x + x = 0 ∨ x + x = point := by decide

theorem point_represented : ∃ x : Mixed, x + x = point := by
  exact ⟨(1, (0, 0)), by decide⟩

theorem point_nonzero : point ≠ 0 := by decide

theorem additive_injection_fixes_point (F : Mixed →+ Mixed)
    (hinjective : Function.Injective F) : F point = point := by
  exact fixes_unique_double point doubled_range point_represented F hinjective

theorem no_fixed_only_zero_injection (F : Mixed →+ Mixed)
    (hinjective : Function.Injective F)
    (hfixed : ∀ y : Mixed, F y = y → y = 0) : False := by
  exact not_fixed_only_zero point doubled_range point_represented point_nonzero F hinjective hfixed

/-- Injection cannot simply be omitted: the zero homomorphism moves `point`. -/
theorem zero_map_moves_point : (0 : Mixed →+ Mixed) point ≠ point := by decide

abbrev Elementary := ZMod 2 × ZMod 2
def missingWitnessPoint : Elementary := (1, 0)
def swap : Elementary ≃+ Elementary := AddEquiv.prodComm (ZMod 2) (ZMod 2)

theorem elementary_doubled_range :
    ∀ x : Elementary, x + x = 0 ∨ x + x = missingWitnessPoint := by decide

theorem swap_injective : Function.Injective swap := swap.injective

theorem swap_moves_unrepresented_point :
    swap missingWitnessPoint ≠ missingWitnessPoint := by decide

theorem chosen_point_not_represented :
    ¬ ∃ x : Elementary, x + x = missingWitnessPoint := by decide

/-- The generic law intentionally also accepts the zero represented point. -/
theorem zero_point_allowed (F : Elementary →+ Elementary)
    (hinjective : Function.Injective F) : F 0 = 0 := by
  exact fixes_unique_double 0 (by decide) ⟨0, by decide⟩ F hinjective

end CryptoLean.UniqueDouble.Examples

#print axioms CryptoLean.UniqueDouble.fixes_unique_double
#print axioms CryptoLean.UniqueDouble.not_fixed_only_zero
#print axioms CryptoLean.UniqueDouble.Examples.additive_injection_fixes_point
#print axioms CryptoLean.UniqueDouble.Examples.no_fixed_only_zero_injection
#print axioms CryptoLean.UniqueDouble.Examples.zero_map_moves_point
#print axioms CryptoLean.UniqueDouble.Examples.swap_moves_unrepresented_point
#print axioms CryptoLean.UniqueDouble.Examples.chosen_point_not_represented
