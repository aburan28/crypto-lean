/-!
# Iteration and return times, without Mathlib

`iterate f n` is `f` applied `n` times, with the same recursion as Mathlib's
`Nat.iterate` (`f^[n+1] x = f^[n] (f x)`). `CryptoLean.Bridge.Iterate` proves
the two equal, so a statement proved here transfers to `f^[n]`.

`Returns f a x` says `x` comes back after `a` steps (Mathlib:
`Function.IsPeriodicPt f a x`). Promoted from
`crypto/research/ghs_cover_census_n5_20261013/lean/CoverCensusN5.lean`
(`Orbit.iter`, `Orbit.Ret`).
-/

namespace CryptoLeanCore

variable {α : Type _} (f : α → α)

/-- `f` applied `n` times. Same recursion as Mathlib's `Nat.iterate`. -/
def iterate : Nat → α → α
  | 0, x => x
  | n + 1, x => iterate n (f x)

theorem iterate_zero (x : α) : iterate f 0 x = x := rfl

theorem iterate_succ (n : Nat) (x : α) : iterate f (n + 1) x = iterate f n (f x) := rfl

theorem iterate_add (a b : Nat) (x : α) :
    iterate f (a + b) x = iterate f b (iterate f a x) := by
  induction a generalizing x with
  | zero => simp [iterate]
  | succ a ih => rw [Nat.succ_add]; exact ih (f x)

/-- `x` returns to itself after `a` steps of `f`. -/
def Returns (a : Nat) (x : α) : Prop := iterate f a x = x

theorem returns_zero (x : α) : Returns f 0 x := rfl

theorem returns_add {a b : Nat} {x : α} (ha : Returns f a x) (hb : Returns f b x) :
    Returns f (a + b) x := by
  unfold Returns at *; rw [iterate_add, ha, hb]

theorem returns_sub {a b : Nat} {x : α} (ha : Returns f a x) (hab : Returns f (a + b) x) :
    Returns f b x := by
  unfold Returns at *; rw [iterate_add, ha] at hab; exact hab

theorem returns_mul {a : Nat} {x : α} (ha : Returns f a x) : ∀ k, Returns f (k * a) x
  | 0 => by simp [Returns, iterate]
  | k + 1 => by rw [Nat.succ_mul]; exact returns_add f (returns_mul ha k) ha

theorem returns_mod {a b : Nat} {x : α} (ha : Returns f a x) (hb : Returns f b x) :
    Returns f (b % a) x := by
  have hm : Returns f (a * (b / a)) x := by rw [Nat.mul_comm]; exact returns_mul f ha _
  have h : a * (b / a) + b % a = b := Nat.div_add_mod b a
  exact returns_sub f hm (by rw [h]; exact hb)

end CryptoLeanCore
