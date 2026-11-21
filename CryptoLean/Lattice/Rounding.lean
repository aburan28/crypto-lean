import Mathlib.Algebra.Order.Round
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Int.GCD

/-!
# Rounding: Learning with Rounding, and ML-KEM compression and decoding

* `lwr_error` (law, any floor field): rounding `x` to the grid `(q/p)ℤ` moves it by at
  most `q/(2p)`. This is why Learning with Rounding (Banerjee–Peikert–Rosen 2012) is
  "LWE with a deterministic error of size `q/(2p)`", and why ML-KEM's ciphertext
  compression adds a bounded error. It is Mathlib's `abs_sub_round`, used as stated.
* `mlkem_compress` / `mlkem_decompress`: FIPS 203 (August 2024) §4.2.1, equations (4.7) and
  (4.8), for `q = 3329`, written in integer arithmetic (`⌈y⌋ = ⌊y + 1/2⌋`).
* `mlkem_decompress_compress_error`: for every `d` used by ML-KEM
  (`d ∈ {1, 4, 5, 10, 11}`) and every `x ∈ [0, q)`, the centred distance between `x` and
  `Decompress_d (Compress_d x)` is at most `⌈q / 2^(d+1)⌋` (FIPS 203 §4.2.1, the bound
  stated after (4.8)). Kernel-checked by `decide` over all 3329 inputs.
* `mlkem_decode_correct`: `Compress_1` recovers the message bit `m` from
  `m·⌈q/2⌋ + e` whenever `|e| < 832 = ⌈q/4⌋`, stated for `ZMod 3329` with the centred
  representative `valMinAbs`. Composed with `decrypt_identity` (`ModuleLWE.lean`) this is
  the per-coefficient correctness condition of ML-KEM decryption.
-/

set_option autoImplicit false

namespace CryptoLean.Lattice

section Law

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-- **LWR error law.** For `p, q > 0`, `(q/p)·⌈p x / q⌋` differs from `x` by at most
`q / (2p)`. -/
theorem lwr_error (q p x : α) (hq : 0 < q) (hp : 0 < p) :
    |(q / p) * (round (p * x / q) : α) - x| ≤ q / (2 * p) := by
  set y := p * x / q with hy
  have hx : x = (q / p) * y := by
    rw [hy]; field_simp
  have hqp : 0 < q / p := div_pos hq hp
  calc |(q / p) * (round y : α) - x|
      = (q / p) * |y - round y| := by
        rw [hx, ← mul_sub, abs_mul, abs_of_pos hqp, abs_sub_comm]
    _ ≤ (q / p) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left (abs_sub_round y) hqp.le
    _ = q / (2 * p) := by field_simp

end Law

section MLKEM

/-- FIPS 203 (4.7) at `q = 3329`: `Compress_d(x) = ⌈(2^d / q)·x⌋ mod 2^d`. -/
def mlkem_compress (d x : ℕ) : ℕ :=
  ((2 ^ d * 2 * x + 3329) / (2 * 3329)) % 2 ^ d

/-- FIPS 203 (4.8) at `q = 3329`: `Decompress_d(y) = ⌈(q / 2^d)·y⌋`. -/
def mlkem_decompress (d y : ℕ) : ℕ :=
  (2 * 3329 * y + 2 ^ d) / (2 ^ d * 2)

/-- Centred distance modulo 3329 between two residues `a, b < 3329`. -/
def centredDist (a b : ℕ) : ℕ :=
  min ((a + 3329 - b) % 3329) ((b + 3329 - a) % 3329)

/-- The FIPS 203 bound `⌈q / 2^(d+1)⌋` for `q = 3329`, as `⌊(q + 2^d) / 2^(d+1)⌋`. -/
def mlkem_compressBound (d : ℕ) : ℕ :=
  (3329 + 2 ^ d) / (2 ^ d * 2)

/-- Checker: every `x < 3329` satisfies the compression error bound for `d`. -/
def compressBoundHolds (d : ℕ) : Bool :=
  (List.range 3329).all fun x =>
    decide (centredDist (mlkem_decompress d (mlkem_compress d x)) x ≤ mlkem_compressBound d)

theorem compressBoundHolds_sound (d : ℕ) (h : compressBoundHolds d = true) (x : ℕ)
    (hx : x < 3329) :
    centredDist (mlkem_decompress d (mlkem_compress d x)) x ≤ mlkem_compressBound d := by
  unfold compressBoundHolds at h
  rw [List.all_eq_true] at h
  simpa using h x (List.mem_range.2 hx)

/-- FIPS 203 §4.2.1: the compression round trip moves `x` by at most `⌈q/2^(d+1)⌋`
(centred, mod `q`) for each `d` ML-KEM uses. The bounds are 832, 104, 52, 2 and 1. -/
theorem mlkem_decompress_compress_error (d : ℕ) (hd : d ∈ ({1, 4, 5, 10, 11} : Finset ℕ))
    (x : ℕ) (hx : x < 3329) :
    centredDist (mlkem_decompress d (mlkem_compress d x)) x ≤ mlkem_compressBound d := by
  refine compressBoundHolds_sound d ?_ x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem mlkem_compressBound_values :
    (mlkem_compressBound 1, mlkem_compressBound 4, mlkem_compressBound 5,
      mlkem_compressBound 10, mlkem_compressBound 11) = (832, 104, 52, 2, 1) := by
  decide

/-- Finite check: for each bit `m` and each shifted noise `k = e + 831 ∈ [0, 1663)`,
`Compress_1` of the residue of `m·1665 + e` is `m`. -/
theorem mlkem_decode_table :
    ∀ m < 2, ∀ k < 1663, mlkem_compress 1 ((m * 1665 + k + 2498) % 3329) = m := by
  decide +kernel

/-- Integer form of 1-bit decoding: if `x ≡ m·1665 + e (mod 3329)` with `|e| < 832`,
then `Compress_1 x = m`. (`1665 = ⌈3329/2⌋`.) -/
theorem mlkem_decode_int (m x : ℕ) (hm : m < 2) (hx : x < 3329) (e : ℤ)
    (he₁ : -832 < e) (he₂ : e < 832)
    (h : (x : ℤ) ≡ (m : ℤ) * 1665 + e [ZMOD 3329]) :
    mlkem_compress 1 x = m := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = (k : ℤ) - 831 := ⟨(e + 831).toNat, by omega⟩
  have hk : k < 1663 := by omega
  have hxk : x = (m * 1665 + k + 2498) % 3329 := by
    unfold Int.ModEq at h; omega
  rw [hxk]
  exact mlkem_decode_table m hm k hk

/-- **ML-KEM decoding is correct for small noise.** In `ZMod 3329`, if
`w = m·1665 + n` with message bit `m` and centred noise `|n| < 832`, then
`Compress_1 (w.val) = m`. With `decrypt_identity`, decryption returns the message
bit whenever each coefficient of the noise `⟪e, r⟫ - ⟪e₁, s⟫ + e₂` (plus the
compression errors) has centred size below 832. -/
theorem mlkem_decode_correct (m : ℕ) (hm : m < 2) (n : ZMod 3329)
    (hn : |n.valMinAbs| < 832) :
    mlkem_compress 1 ((m : ZMod 3329) * 1665 + n).val = m := by
  set w : ZMod 3329 := (m : ZMod 3329) * 1665 + n
  refine mlkem_decode_int m w.val hm (ZMod.val_lt w) n.valMinAbs ?_ ?_ ?_
  · have := (abs_lt.1 hn).1; omega
  · exact (abs_lt.1 hn).2
  · have h := (ZMod.intCast_eq_intCast_iff (w.val : ℤ) ((m : ℤ) * 1665 + n.valMinAbs) 3329).1
      (by push_cast; simp only [ZMod.natCast_zmod_val, w])
    exact_mod_cast h

end MLKEM

end CryptoLean.Lattice
