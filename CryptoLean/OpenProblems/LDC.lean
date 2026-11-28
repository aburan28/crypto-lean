import Mathlib

/-!
# Locally decodable codes: open problem #226

## Model

A binary code with `k` message bits and codeword positions indexed by a finite type `ι`
(blocklength `N = |ι|`) is an encoding map `enc : (Fin k → ZMod 2) → (ι → ZMod 2)`.
`IsLDC enc q δ ε` says that `enc` is a `(q, δ, ε)`-locally decodable code: there is a
finite, uniformly distributed random seed space `Ω` and, for every message index `i`, a
non-adaptive decoder that on seed `r` reads the `q` positions `Q i r 0, …, Q i r (q-1)` of
the received word and outputs `D i r (those q bits)`; for every message `x`, every word `w`
within Hamming distance `δ·N` of `enc x` and every `i`, the decoder outputs `x i` on at
least a `1/2 + ε` fraction of the seeds.

Modelling simplifications (all standard, none affects the constant-query / polynomial-length
question up to changing constants):
* the decoder is **non-adaptive** (it fixes its `q` query positions from the seed before
  reading); an adaptive `q`-query decoder can be made non-adaptive with at most `2^q - 1`
  queries, and Katz–Trevisan show the success advantage degrades only by constant factors;
* the decoder's randomness is a **uniform seed over a finite set**, so all success
  probabilities are rational; any decoder with finitely supported randomness is
  approximated arbitrarily well this way;
* "at most `q` queries" is modelled as exactly `q` query positions (repetitions allowed).

## Contents

* `ConstantQueryPolyLDC` – the existence half of open problem #226 as an unproved `Prop`.
  The problem asks to *decide* it (construct such a family or prove none exists); it is
  **not** resolved here, and neither it nor its negation is proved.
* Proved known results about the Hadamard code `had x a = ⟨a, x⟩` (blocklength `2^k`):
  linearity (`hadamard_add`), relative distance exactly `1/2` (`two_mul_hammingDist_hadamard`),
  the union-bound counting statement for the 2-query decoder
  (`card_hadamard_decoder_errors_le`), and that it is a `(2, δ, ε)`-LDC whenever
  `2δ + ε ≤ 1/2` (`isLDC_hadamard`).

The Hadamard code has **exponential** length `2^k`, so these results say nothing about the
polynomial-length question. Known but **not formalized** here: for `q = 2`, every 2-query
LDC has length `2^{Ω(k)}` (Goldreich–Karloff–Schulman–Trevisan 2002 for linear codes,
Kerenidis–de Wolf 2003 for all codes via a quantum argument), so 2 queries cannot give
polynomial length; for general constant `q`, Katz–Trevisan (2000) prove only polynomial
lower bounds `N ≥ k^{q/(q-1)}`-type (improved for `q = 3` to roughly `k^3` by Alrabiah,
Guruswami, Kothari, Manohar 2023), while the best constructions (Yekhanin 2008,
Efremenko 2009) have subexponential but super-polynomial length.
-/

namespace CryptoLean.OpenProblems.LDC

open Finset

/-! ## Locally decodable codes -/

/-- `enc` is a `(q, δ, ε)`-locally decodable code (non-adaptive, uniform finite seed space).
See the module docstring for the modelling simplifications. -/
def IsLDC {k : ℕ} {ι : Type} [Fintype ι] (enc : (Fin k → ZMod 2) → ι → ZMod 2)
    (q : ℕ) (δ ε : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (_ : Nonempty Ω)
    (Q : Fin k → Ω → Fin q → ι) (D : Fin k → Ω → (Fin q → ZMod 2) → ZMod 2),
    ∀ (x : Fin k → ZMod 2) (w : ι → ZMod 2),
      (hammingDist w (enc x) : ℝ) ≤ δ * Fintype.card ι →
      ∀ i : Fin k,
        (1 / 2 + ε) * Fintype.card Ω ≤
          ((univ.filter fun r => D i r (fun j => w (Q i r j)) = x i).card : ℝ)

/-- **Open problem #226 (ProofAtlas, edition 2026-11-12): constant-query locally decodable
codes with polynomial blocklength.** Exact statement:
"Construct binary codes of blocklength polynomial in the message length that permit
recovery of any message bit with a constant number of queries from words corrupted in a
constant fraction of positions, or prove that no such family exists."

This `Prop` is the existence alternative: there are a constant query count `q`, a constant
corruption fraction `δ > 0`, a constant advantage `ε > 0` and a polynomial bound
`N ≤ c·k^d + c` such that for every message length `k` some binary code
`(Fin k → ZMod 2) → (Fin N → ZMod 2)` is a `(q, δ, ε)`-LDC. The open problem is to prove
this `Prop` or its negation; it is widely conjectured false but is **OPEN**, and nothing
here proves either. Modelling: as in `IsLDC` (non-adaptive decoder, uniform finite seed
space, success probability `≥ 1/2 + ε` on every bit for every word within relative distance
`δ`); the polynomial is written as `c·k^d + c` with natural `c, d`, which bounds every
polynomial with natural coefficients and is itself one. -/
def ConstantQueryPolyLDC : Prop :=
  ∃ (q : ℕ) (δ ε : ℝ), 0 < δ ∧ 0 < ε ∧ ∃ c d : ℕ, ∀ k : ℕ,
    ∃ N : ℕ, N ≤ c * k ^ d + c ∧
      ∃ enc : (Fin k → ZMod 2) → Fin N → ZMod 2, IsLDC enc q δ ε

/-! ## The Hadamard code -/

/-- The Hadamard code: the codeword of `x` lists `⟨a, x⟩` for all `a ∈ 𝔽₂ᵏ`
(blocklength `2^k`, exponential in `k`). -/
def hadamard {k : ℕ} (x : Fin k → ZMod 2) : (Fin k → ZMod 2) → ZMod 2 :=
  fun a => a ⬝ᵥ x

/-- **Known result** (folklore; e.g. Arora–Barak, *Computational Complexity*, §19.2):
the Hadamard code is linear. -/
theorem hadamard_add {k : ℕ} (x y : Fin k → ZMod 2) :
    hadamard (x + y) = hadamard x + hadamard y := by
  funext a; simp [hadamard, dotProduct_add]

theorem card_hadamard_cube (k : ℕ) : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
  simp

theorem zmod2_ne_zero_iff (z : ZMod 2) : z ≠ 0 ↔ z = 1 := by
  revert z; decide

/-- **Known result** (folklore; Arora–Barak §19.2, MacWilliams–Sloane Ch. 1): distinct
Hadamard codewords differ in exactly half of the `2^k` positions, i.e. the code has
relative distance `1/2`. Stated as `2·d(had x, had y) = 2^k`. -/
theorem two_mul_hammingDist_hadamard {k : ℕ} {x y : Fin k → ZMod 2} (hxy : x ≠ y) :
    2 * hammingDist (hadamard x) (hadamard y) = 2 ^ k := by
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp hxy
  set e : Fin k → ZMod 2 := Pi.single j 1
  set S := univ.filter fun a : Fin k → ZMod 2 => hadamard x a ≠ hadamard y a
  have hd : hammingDist (hadamard x) (hadamard y) = S.card := rfl
  have key : ∀ a, hadamard x (a + e) - hadamard y (a + e)
      = (hadamard x a - hadamard y a) + 1 := by
    intro a
    have : x j - y j = 1 := (zmod2_ne_zero_iff _).mp (sub_ne_zero.mpr hj)
    simp only [hadamard, add_dotProduct, e, single_dotProduct, one_mul]
    rw [← this]; ring
  have hee : e + e = 0 := by
    ext t; simp only [e, Pi.add_apply, Pi.single_apply, Pi.zero_apply]
    split_ifs <;> decide
  have hc : (univ.filter fun a : Fin k → ZMod 2 => ¬ (hadamard x a ≠ hadamard y a)).card
      = S.card := by
    apply Finset.card_nbij' (fun a => a + e) (fun a => a + e)
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not] at ha ⊢
      simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      intro h
      have := key a
      rw [ha, h, sub_self, sub_self, zero_add] at this
      exact one_ne_zero this.symm
    · intro a ha
      simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, not_not] at ha ⊢
      have := key a
      rw [← sub_ne_zero] at ha
      rw [(zmod2_ne_zero_iff _).mp ha] at this
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      rw [h2] at this
      exact sub_eq_zero.mp this
    · intro a _; simp [add_assoc, hee]
    · intro a _; simp [add_assoc, hee]
  have htot := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin k → ZMod 2))) (fun a => hadamard x a ≠ hadamard y a)
  rw [hc, card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  rw [hd, two_mul]; convert htot using 2

/-- The standard 2-query decoder for bit `i`: on seed `a`, query `a` and `a + eᵢ` and output
the difference. -/
def hadQuery {k : ℕ} (i : Fin k) (a : Fin k → ZMod 2) : Fin 2 → (Fin k → ZMod 2) :=
  ![a, a + Pi.single i 1]

/-- Decoding function of the 2-query Hadamard decoder. -/
def hadDecode (u : Fin 2 → ZMod 2) : ZMod 2 := u 1 - u 0

/-- **Known result** (Blum–Luby–Rubinfeld 1993 self-correction; Arora–Barak §19.2,
Yekhanin's survey "Locally decodable codes" 2012, §2): union bound for the 2-query
Hadamard decoder. If `w` differs from `had x` in `t` positions, then the number of seeds
`a ∈ 𝔽₂ᵏ` on which the decoder (query `w a`, `w (a + eᵢ)`, output their difference) does
**not** return `x i` is at most `2t`. -/
theorem card_hadamard_decoder_errors_le {k : ℕ} (x : Fin k → ZMod 2)
    (w : (Fin k → ZMod 2) → ZMod 2) (i : Fin k) :
    (univ.filter fun a => hadDecode (fun j => w (hadQuery i a j)) ≠ x i).card ≤
      2 * hammingDist w (hadamard x) := by
  set e : Fin k → ZMod 2 := Pi.single i 1
  set B := univ.filter fun a => w a ≠ hadamard x a with hB
  have hd : hammingDist w (hadamard x) = B.card := rfl
  have hsub : (univ.filter fun a => hadDecode (fun j => w (hadQuery i a j)) ≠ x i) ⊆
      B ∪ B.image (fun b => b - e) := by
    intro a ha
    have ha' : w (a + e) - w a ≠ x i := by
      have := (mem_filter.mp ha).2
      simpa [hadDecode, hadQuery] using this
    by_contra hn
    simp only [mem_union, mem_filter, mem_univ, true_and, mem_image, hB, not_or, not_not,
      not_exists, not_and] at hn
    obtain ⟨h1, h2⟩ := hn
    have h3 : w (a + e) = hadamard x (a + e) := by
      by_contra h; exact h2 (a + e) h (by simp)
    apply ha'
    rw [h3, h1]
    simp [hadamard, add_dotProduct, e]
  calc _ ≤ (B ∪ B.image (fun b => b - e)).card := card_le_card hsub
    _ ≤ B.card + (B.image (fun b => b - e)).card := card_union_le _ _
    _ ≤ B.card + B.card := Nat.add_le_add_left card_image_le _
    _ = _ := by rw [hd]; ring

/-- **Known result** (Arora–Barak §19.2; Yekhanin 2012, §2; Katz–Trevisan 2000): the
Hadamard code is a 2-query locally decodable code: on any word within relative distance `δ`
of a codeword, the decoder succeeds with probability `≥ 1 − 2δ`, so it is a
`(2, δ, ε)`-LDC whenever `2δ + ε ≤ 1/2`. Its blocklength is `2^k` (exponential), so this
does **not** bear on the polynomial-length question #226. -/
theorem isLDC_hadamard {k : ℕ} {δ ε : ℝ} (h : 2 * δ + ε ≤ 1 / 2) :
    IsLDC (hadamard (k := k)) 2 δ ε := by
  refine ⟨Fin k → ZMod 2, inferInstance, inferInstance, hadQuery, fun _ _ => hadDecode, ?_⟩
  intro x w hw i
  have herr := card_hadamard_decoder_errors_le x w i
  have htot := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin k → ZMod 2)))
    (fun a => hadDecode (fun j => w (hadQuery i a j)) = x i)
  rw [card_univ] at htot
  have herr' : ((univ.filter fun a => ¬ hadDecode (fun j => w (hadQuery i a j)) = x i).card : ℝ)
      ≤ 2 * (hammingDist w (hadamard x) : ℝ) := by exact_mod_cast herr
  have htot' : ((univ.filter fun a => hadDecode (fun j => w (hadQuery i a j)) = x i).card : ℝ)
      + ((univ.filter fun a => ¬ hadDecode (fun j => w (hadQuery i a j)) = x i).card : ℝ)
      = (Fintype.card (Fin k → ZMod 2) : ℝ) := by exact_mod_cast htot
  have hN : (0 : ℝ) ≤ Fintype.card (Fin k → ZMod 2) := Nat.cast_nonneg _
  nlinarith

#print axioms hadamard_add
#print axioms two_mul_hammingDist_hadamard
#print axioms card_hadamard_decoder_errors_le
#print axioms isLDC_hadamard

end CryptoLean.OpenProblems.LDC
