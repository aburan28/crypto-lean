import Mathlib.Algebra.Group.Hom.Instances

/-!
# The unique represented doubled point is fixed by additive injections

This is a point-group law over inherited Mathlib structures. It does not
assert that a geometric kernel has this doubled-image contract.
-/
set_option autoImplicit false

namespace CryptoLean.UniqueDouble

variable {M : Type*} [AddMonoid M]

/-- If all doubles lie in `{0, p}` and `p` is a double, every injective
additive endomorphism fixes `p`. The degenerate case `p = 0` is allowed. -/
theorem fixes_unique_double (p : M)
    (hdoubles : ∀ x : M, x + x = 0 ∨ x + x = p)
    (hrepresented : ∃ x : M, x + x = p)
    (F : M →+ M) (hinjective : Function.Injective F) : F p = p := by
  obtain ⟨x, hx⟩ := hrepresented
  have hmap : F p = F x + F x := by rw [← hx, map_add]
  rcases hdoubles (F x) with hz | hp
  · have hpzero : p = 0 := hinjective (by
      calc
        F p = 0 := hmap.trans hz
        _ = F 0 := (map_zero F).symm)
    rw [hpzero, map_zero]
  · exact hmap.trans hp

/-- The nonzero represented double obstructs fixed-only-zero additive
injections. Nonzeroness is needed here, rather than in the fixed-point law. -/
theorem not_fixed_only_zero (p : M)
    (hdoubles : ∀ x : M, x + x = 0 ∨ x + x = p)
    (hrepresented : ∃ x : M, x + x = p) (hnonzero : p ≠ 0)
    (F : M →+ M) (hinjective : Function.Injective F)
    (hfixed : ∀ y : M, F y = y → y = 0) : False := by
  exact hnonzero (hfixed p (fixes_unique_double p hdoubles hrepresented F hinjective))

end CryptoLean.UniqueDouble
