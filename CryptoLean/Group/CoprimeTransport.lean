import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace CryptoLean.Transport
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The concrete integer coefficient used to undo multiplication by d. -/
def recoveryCoefficient (r d : ℕ) : ℤ := Nat.gcdB r d

theorem recoveryCoefficient_recovers (S : AddSubgroup A) [Finite S] (d : ℕ)
    (hc : (Nat.card S).Coprime d) (P : S) :
    recoveryCoefficient (Nat.card S) d • (d • P) = P := by
  have hcard : (Nat.card S : ℤ) • P = 0 := by simp
  have hbez := Nat.gcd_eq_gcd_ab (Nat.card S) d
  rw [hc.gcd_eq_one] at hbez
  have hsum : Nat.gcdA (Nat.card S) d * (Nat.card S : ℤ) +
      Nat.gcdB (Nat.card S) d * (d : ℤ) = 1 := by
    calc
      _ = (Nat.card S : ℤ) * Nat.gcdA (Nat.card S) d +
          (d : ℤ) * Nat.gcdB (Nat.card S) d := by ring
      _ = 1 := hbez.symm
  unfold recoveryCoefficient
  calc
    _ = (Nat.gcdA (Nat.card S) d * (Nat.card S : ℤ) +
        Nat.gcdB (Nat.card S) d * (d : ℤ)) • P := by
      simp [add_zsmul, mul_zsmul, hcard]
    _ = P := by rw [hsum]; simp

/-- Recovery from an explicitly supplied reverse composition. This proves
algebraic recovery, not construction or evaluation cost of geometric maps. -/
theorem recover_reverse_composition (S : AddSubgroup A) [Finite S]
    (f : A →+ B) (back : B →+ A) (d : ℕ)
    (hc : (Nat.card S).Coprime d)
    (hdual : ∀ P : S, back (f P) = d • (P : A)) (P : S) :
    recoveryCoefficient (Nat.card S) d • back (f P) = (P : A) := by
  rw [hdual]
  exact congrArg Subtype.val (recoveryCoefficient_recovers S d hc P)


theorem injective_on_subgroup (S : AddSubgroup A) [Finite S]
    (f : A →+ B) (back : B →+ A) (d : ℕ)
    (hc : (Nat.card S).Coprime d)
    (hdual : ∀ P : S, back (f P) = d • (P : A)) :
    Function.Injective (fun P : S => f P) := by
  intro P Q h
  change f (P : A) = f (Q : A) at h
  apply Subtype.ext
  rw [← recover_reverse_composition S f back d hc hdual P,
    ← recover_reverse_composition S f back d hc hdual Q, h]

theorem dlog_transport_iff (S : AddSubgroup A) [Finite S]
    (f : A →+ B) (back : B →+ A) (d : ℕ)
    (hc : (Nat.card S).Coprime d)
    (hdual : ∀ P : S, back (f P) = d • (P : A))
    (G Q : S) (k : ℤ) :
    k • f (G : A) = f (Q : A) ↔ k • G = Q := by
  constructor
  · intro h
    apply injective_on_subgroup S f back d hc hdual
    simpa using h
  · intro h
    simpa using congrArg (fun P : S => f (P : A)) h
end CryptoLean.Transport
