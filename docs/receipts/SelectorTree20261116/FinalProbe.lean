import CryptoLean.Group.ShortlistCompletion
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
noncomputable section

example (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve.Affine (ZMod p))
    (H : AddSubgroup W.Point) {A : Type*} [Fintype A] {s b : ℕ} (hs : 0 < s)
    (F : A → Finset H) (L : ℕ) (hcap : ∀ a, (F a).card ≤ L) :
    Nat.card {ω : A × ((Fin s × Fin b) → H) // ∃ g ∈ F ω.1,
      ∃ c : Fin s → Fin b, CryptoLean.PartiteCoverage.tupleSum c ω.2 = g} * Nat.card H ≤
        Nat.card A * L * b ^ s * (Nat.card H) ^ (s * b) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Finite W.Point := Finite.of_equiv
    (Option {xy : ZMod p × ZMod p // W.Nonsingular xy.1 xy.2})
    W.nonsingularPointEquiv.symm
  letI : Fintype H := Fintype.ofFinite H
  exact CryptoLean.ShortlistCompletion.partite_shortlist_count hs F L hcap

example {G : Type*} [AddCommGroup G] [Fintype G] {s b : ℕ}
    (hs : 0 < s) (c : Fin s → Fin b) (g : G) :
    Nat.card {x : (Fin s × Fin b) → G // CryptoLean.PartiteCoverage.tupleSum c x = g} *
      Nat.card G = (Nat.card G) ^ (s * b) := by
  simpa only [Nat.card_fun, Nat.card_prod, Nat.card_fin] using
    CryptoLean.ShortlistCompletion.fiber_card_mul (CryptoLean.PartiteCoverage.tupleSum c)
      (CryptoLean.PartiteCoverage.tupleSum_surjective c hs) g
