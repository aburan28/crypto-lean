import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.NormNum.Prime

/-!
# NTT parameters of ML-KEM and ML-DSA

The number-theoretic transform of `R_q = Z_q[X]/(X^256 + 1)` needs a primitive
`2^k`-th root of unity in `Z_q`. Instance obligations for the two NIST standards:

* ML-KEM (FIPS 203 §4.3): `q = 3329` is prime and `ζ = 17` is a primitive 256th root of
  unity (`mlkem_zeta`). There is **no** primitive 512th root (`mlkem_no_512th_root`,
  since `3328 = 2^8 · 13`), so `X^256 + 1` does not split into linear factors mod 3329:
  ML-KEM's NTT is "incomplete" and stops at 128 quadratic factors `X^2 - ζ^(2·brv(i)+1)`.
* ML-DSA (FIPS 204 §7.5): `q = 8380417 = 2^23 - 2^13 + 1` is prime and `ζ = 1753` is a
  primitive 512th root of unity (`mldsa_zeta`), so `X^256 + 1` splits completely.

The order is read off with Mathlib's `orderOf_eq_prime_pow` (as stated) from two
power evaluations; non-existence uses `ZMod.orderOf_dvd_card_sub_one`.
-/

set_option autoImplicit false

namespace CryptoLean.Lattice

theorem mlkem_q_prime : Nat.Prime 3329 := by norm_num

theorem mldsa_q_prime : Nat.Prime 8380417 := by norm_num

theorem mldsa_q_eq : 8380417 = 2 ^ 23 - 2 ^ 13 + 1 := by norm_num

/-- Law: in a monoid, if `x^(2^k) ≠ 1` and `x^(2^(k+1)) = 1` then `x` is a primitive
`2^(k+1)`-th root of unity. -/
theorem isPrimitiveRoot_two_pow {M : Type*} [CommMonoid M] (x : M) (k : ℕ)
    (h₁ : ¬x ^ 2 ^ k = 1) (h₂ : x ^ 2 ^ (k + 1) = 1) : IsPrimitiveRoot x (2 ^ (k + 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← orderOf_eq_prime_pow h₁ h₂]
  exact IsPrimitiveRoot.orderOf x

/-- Transfer a `Nat` power residue to `ZMod`. -/
theorem zmod_pow_eq_of_nat {q a e r : ℕ} (h : a ^ e % q = r) :
    (a : ZMod q) ^ e = (r : ZMod q) := by
  rw [← h, ZMod.natCast_mod]; push_cast; rfl

/-- FIPS 203: `17` is a primitive 256th root of unity mod 3329. -/
theorem mlkem_zeta : IsPrimitiveRoot (17 : ZMod 3329) 256 := by
  have h₁ : (17 : ZMod 3329) ^ 2 ^ 7 = ((3328 : ℕ) : ZMod 3329) :=
    zmod_pow_eq_of_nat (by norm_num)
  have h₂ : (17 : ZMod 3329) ^ 2 ^ 8 = ((1 : ℕ) : ZMod 3329) :=
    zmod_pow_eq_of_nat (by norm_num)
  refine isPrimitiveRoot_two_pow (17 : ZMod 3329) 7 ?_ (by simpa using h₂)
  rw [h₁]; decide

/-- `X^256 + 1` has no root of order 512 mod 3329, because 512 does not divide 3328. -/
theorem mlkem_no_512th_root (ζ : ZMod 3329) : ¬IsPrimitiveRoot ζ 512 := by
  have : Fact (Nat.Prime 3329) := ⟨mlkem_q_prime⟩
  intro h
  have hne : ζ ≠ 0 := h.ne_zero (by norm_num)
  have hdvd := ZMod.orderOf_dvd_card_sub_one hne
  rw [← h.eq_orderOf] at hdvd
  norm_num at hdvd

/-- `3329 ≡ 1 (mod 256)` but not `(mod 512)`: the arithmetic behind the two facts above. -/
theorem mlkem_q_mod : 3329 % 256 = 1 ∧ 3329 % 512 ≠ 1 := by decide

/-- FIPS 204: `1753` is a primitive 512th root of unity mod 8380417. -/
theorem mldsa_zeta : IsPrimitiveRoot (1753 : ZMod 8380417) 512 := by
  have h₁ : (1753 : ZMod 8380417) ^ 2 ^ 8 = ((8380416 : ℕ) : ZMod 8380417) :=
    zmod_pow_eq_of_nat (by norm_num)
  have h₂ : (1753 : ZMod 8380417) ^ 2 ^ 9 = ((1 : ℕ) : ZMod 8380417) := by
    rw [pow_succ, pow_mul, h₁]; decide
  refine isPrimitiveRoot_two_pow (1753 : ZMod 8380417) 8 ?_ (by simpa using h₂)
  rw [h₁]; decide

end CryptoLean.Lattice
