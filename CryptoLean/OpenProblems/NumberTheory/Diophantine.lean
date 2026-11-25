import Mathlib

/-!
# Open problems about Diophantine equations (abc family)

ProofAtlas problems (releaseRank) 9, 86, 321, 344, 372, 395, 493.

**All seven problems are OPEN.** Each one that Mathlib can express appears below only as an
unproved `def … : Prop` whose docstring quotes the ProofAtlas `exactTarget` and lists the
modelling choices. Nothing in this file proves, or claims progress towards, any of them.
Finite verifications are labelled as finite checks; they are not partial progress on the
infinite statements.

Mathlib objects reused (no re-definitions):
* `UniqueFactorizationMonoid.radical` (on `ℕ`, `Nat.radical_eq_prod_primeFactors`);
* `Polynomial.abc` (Mason–Stothers theorem);
* `FermatLastTheoremFor`, `fermatLastTheoremThree`, `fermatLastTheoremFour`,
  `fermatLastTheoremWith_of_fermatLastTheoremWith_coprime`.

## What is missing from Mathlib (gap notes)

* **Problem 86 (Szpiro's conjecture over `ℚ`) is not stated here.** Mathlib has Weierstrass
  curves, their discriminant `WeierstrassCurve.Δ`, and *local* minimal models
  (`WeierstrassCurve.IsMinimal R W` over the fraction field of a DVR `R`, with
  `exists_isMinimal`). It does not have
  (1) the *global* minimal discriminant `Δ_E` of an elliptic curve over `ℚ` (existence of a
      global minimal model over a PID, or the product `∏_p p^{v_p(Δ_min,p)}` assembled from
      the local minimal models), nor
  (2) the **conductor** `N_E` (the exponents `f_p`, including the wild part at `p = 2, 3`
      given by Ogg's formula / the Swan conductor of the `ℓ`-adic Tate module).
  Replacing `N_E` by `rad(Δ_E)` would give a different (stronger, non-equivalent) statement,
  so no weaker Prop is offered.
* **Mihăilescu's theorem (Catalan's conjecture, the `k = 1` case of Pillai)**, the
  **Darmon–Granville theorem** (finiteness for fixed hyperbolic `(p,q,r)`) and
  **Danilov's theorem** (the exponent `1/2` in Hall's conjecture is optimal) are not in
  Mathlib and are *not* formalised here.

## Known results proved here

* `masonStothers` — Mason–Stothers (polynomial abc), restated from Mathlib.
* `abc_implies_eventually_FLT` — abc implies Fermat's Last Theorem for all large exponents
  (an implication between statements; it does not prove abc or FLT).
* `beal_implies_FLT` — Beal's conjecture implies FLT for every exponent `≥ 3` (implication).
* `beal_exponent_three`, `beal_exponent_four` — the cases `x = y = z = 3` and `x = y = z = 4`
  of Beal's conjecture (Euler / Fermat, via Mathlib's FLT for 3 and 4).
* `not_sum_three_cubes_of_mod_nine` — `k ≡ 4, 5 (mod 9)` is not a sum of three integer cubes.
* `threeCubes_infinite_one`, `threeCubes_infinite_two` — Heath-Brown's refinement holds for
  `k = 1` (Mahler 1936) and `k = 2` (Werebrusow 1908) by polynomial identities.
* `pillai_squares_finite` — for `k ≥ 1` there are finitely many `(x, y)` with `x² − y² = k`.

## Finite checks (explicit identities, labelled as such)

* `threeCubes_le_twenty` — every `0 ≤ k ≤ 20` with `k ≢ 4, 5 (mod 9)` is a sum of three cubes.
* `threeCubes_thirtyThree`, `threeCubes_fortyTwo` — Booker's (2019) and Booker–Sutherland's
  (2021) representations of 33 and 42.
* `beal_common_factor_examples`, `beal_needs_exponent_gt_two` — Beal-type equalities.
* `fermatCatalan_known_solutions` — known members of the Fermat–Catalan solution set.
* `abc_reyssat_triple` — Reyssat's high-quality abc triple `2 + 3¹⁰·109 = 23⁵`.
* `hall_example_5234` — `378661² − 5234³ = 17`.
* `pillai_catalan_example` — `3² − 2³ = 1`.
-/

namespace CryptoLean.OpenProblems.NumberTheory.Diophantine

open UniqueFactorizationMonoid

/-! ## Problem 9: the abc conjecture -/

/-- **Open problem (ProofAtlas rank 9, the abc conjecture of Masser and Oesterlé).**

ProofAtlas exactTarget: "Prove that for every epsilon > 0, there exists a constant C(epsilon)
such that for all coprime positive integers a + b = c, c < C(epsilon) rad(abc)^{1+epsilon}."

Modelling choices:
* `ε` and `C` are real numbers; `rad` is Mathlib's `UniqueFactorizationMonoid.radical` on `ℕ`
  (the product of the distinct primes dividing the argument), and the power is `Real.rpow`.
* "coprime" is `Nat.Coprime a b`; together with `a + b = c` this is equivalent to pairwise
  coprimality of `a, b, c`.
* `C` is not required to be positive explicitly; positivity is forced by any instance
  (e.g. `1 + 1 = 2`). -/
def abcConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) < C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε)

/-- **Known result** (Mason 1984, Stothers 1981; Mathlib's `Polynomial.abc`): the polynomial
abc theorem. For nonzero polynomials `a, b, c` over a field with `a, b` coprime and
`a + b + c = 0`, each of `deg a, deg b, deg c` is less than `deg rad(abc)`, unless all three
derivatives vanish. -/
theorem masonStothers {k : Type*} [Field k] [DecidableEq k] {a b c : Polynomial k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree) ∨
      (Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧
        Polynomial.derivative c = 0) :=
  Polynomial.abc ha hb hc hab hsum

/-- **Finite check** (Reyssat's abc triple): `a = 2`, `b = 3¹⁰·109`, `c = 23⁵` are coprime with
`a + b = c`, `rad(abc) = 15042`, and `c² > rad(abc)³` (i.e. `c > rad(abc)^{3/2}`). This
is one explicit triple and says nothing about the conjecture. -/
theorem abc_reyssat_triple :
    Nat.Coprime 2 (3 ^ 10 * 109) ∧ 2 + 3 ^ 10 * 109 = 23 ^ 5 ∧
      radical (2 * (3 ^ 10 * 109) * 23 ^ 5) = 15042 ∧
      (23 ^ 5) ^ 2 > (radical (2 * (3 ^ 10 * 109) * 23 ^ 5)) ^ 3 := by
  have hrad : radical (2 * (3 ^ 10 * 109) * 23 ^ 5) = 15042 := by
    rw [Nat.radical_eq_prod_primeFactors]
    have h2 : Nat.Prime 2 := by norm_num
    have h3 : Nat.Prime 3 := by norm_num
    have h109 : Nat.Prime 109 := by norm_num
    have h23 : Nat.Prime 23 := by norm_num
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      h2.primeFactors, h3.primeFactors, h109.primeFactors, h23.primeFactors]
    decide
  refine ⟨by norm_num, by norm_num, hrad, ?_⟩
  rw [hrad]; norm_num

/-- If `a^n + b^n = c^n` and no prime divides all of `a, b, c`, then `a` and `b` are coprime. -/
private lemma coprime_of_fermat {a b c n : ℕ} (hn : 0 < n) (h : a ^ n + b ^ n = c ^ n)
    (hg : ({a, b, c} : Finset ℕ).gcd id = 1) : Nat.Coprime a b := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have hpc : p ∣ c := by
    apply hp.dvd_of_dvd_pow (n := n)
    rw [← h]
    exact dvd_add (dvd_pow hpa hn.ne') (dvd_pow hpb hn.ne')
  have : p ∣ ({a, b, c} : Finset ℕ).gcd id := by
    apply Finset.dvd_gcd
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  rw [hg] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Known result (implication)** (folklore; see e.g. Granville–Tucker, *It's as easy as abc*,
Notices AMS 2002): the abc conjecture implies Fermat's Last Theorem for all sufficiently large
exponents. This is an implication between statements; it proves neither. -/
theorem abc_implies_eventually_FLT (habc : abcConjecture) :
    ∃ N : ℕ, ∀ n ≥ N, FermatLastTheoremFor n := by
  obtain ⟨C, hC⟩ := habc 1 one_pos
  refine ⟨7 + ⌈C⌉₊, fun n hn => ?_⟩
  rw [fermatLastTheoremFor_iff_nat]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hg h
  have hn0 : 0 < n := by omega
  have hcop : Nat.Coprime a b := coprime_of_fermat hn0 h hg
  have ha0 : 0 < a := Nat.pos_of_ne_zero ha
  have hb0 : 0 < b := Nat.pos_of_ne_zero hb
  have hc0 : 0 < c := Nat.pos_of_ne_zero hc
  have key := hC (a ^ n) (b ^ n) (c ^ n) (pow_pos ha0 n) (pow_pos hb0 n)
    (Nat.Coprime.pow n n hcop) h
  -- a < c and b < c
  have hac : a < c := by
    by_contra hh
    push Not at hh
    have : c ^ n ≤ a ^ n := Nat.pow_le_pow_left hh n
    have : 0 < b ^ n := pow_pos hb0 n
    omega
  have hbc : b < c := by
    by_contra hh
    push Not at hh
    have : c ^ n ≤ b ^ n := Nat.pow_le_pow_left hh n
    have : 0 < a ^ n := pow_pos ha0 n
    omega
  -- rad(a^n b^n c^n) = rad(abc) ≤ abc < c^3
  have hrad : radical (a ^ n * b ^ n * c ^ n) = radical (a * b * c) := by
    rw [← mul_pow, ← mul_pow, radical_pow _ hn0.ne']
  have hrad_le : radical (a * b * c) ≤ a * b * c :=
    Nat.radical_le_self_iff.mpr (by positivity)
  have habc3 : a * b * c < c ^ 3 := by
    have : a * b < c * c := Nat.mul_lt_mul'' hac hbc
    calc a * b * c < c * c * c := Nat.mul_lt_mul_of_pos_right this hc0
      _ = c ^ 3 := by ring
  rw [hrad] at key
  have hR : ((radical (a * b * c) : ℕ) : ℝ) ≤ (c : ℝ) ^ 3 := by
    exact_mod_cast (hrad_le.trans habc3.le)
  have hRpos : (0 : ℝ) ≤ ((radical (a * b * c) : ℕ) : ℝ) := by positivity
  have h2 : ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + (1 : ℝ)) ≤ (c : ℝ) ^ 6 := by
    rw [show (1 + (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc ((radical (a * b * c) : ℕ) : ℝ) ^ 2 ≤ ((c : ℝ) ^ 3) ^ 2 :=
          pow_le_pow_left₀ hRpos hR 2
      _ = (c : ℝ) ^ 6 := by ring
  have hc2 : (2 : ℝ) ≤ c := by exact_mod_cast (show 2 ≤ c by omega)
  have hCpos : 0 < C := by
    by_contra hh
    push Not at hh
    have : C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + (1 : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hh (by positivity)
    have : (0 : ℝ) < ((c ^ n : ℕ) : ℝ) := by positivity
    linarith
  have hlt : ((c : ℝ) ^ 6) * (c : ℝ) ^ (n - 6) < C * (c : ℝ) ^ 6 := by
    rw [← pow_add, show 6 + (n - 6) = n by omega]
    calc (c : ℝ) ^ n = ((c ^ n : ℕ) : ℝ) := by push_cast; ring
      _ < C * ((radical (a * b * c) : ℕ) : ℝ) ^ (1 + (1 : ℝ)) := key
      _ ≤ C * (c : ℝ) ^ 6 := mul_le_mul_of_nonneg_left h2 hCpos.le
  have hc6 : (0 : ℝ) < (c : ℝ) ^ 6 := by positivity
  have hlt' : (c : ℝ) ^ (n - 6) < C := by nlinarith
  have hm : ⌈C⌉₊ < n - 6 := by omega
  have h2m : ((⌈C⌉₊ : ℕ) : ℝ) < (2 : ℝ) ^ (n - 6) := by
    have : ⌈C⌉₊ < 2 ^ (n - 6) := lt_trans hm (Nat.lt_two_pow_self)
    exact_mod_cast this
  have hpow : (2 : ℝ) ^ (n - 6) ≤ (c : ℝ) ^ (n - 6) := pow_le_pow_left₀ (by norm_num) hc2 _
  have := Nat.le_ceil C
  linarith

/-! ## Problem 86: Szpiro's conjecture

Not stated: see the gap note in the module docstring (Mathlib lacks the global minimal
discriminant and the conductor of an elliptic curve over `ℚ`). -/

/-! ## Problem 321: Beal's conjecture -/

/-- **Open problem (ProofAtlas rank 321, Beal's conjecture / Tijdeman–Zagier).**

ProofAtlas exactTarget: "Prove that if A^x + B^y = C^z with A, B, C, x, y, z positive integers
and x, y, z all greater than 2, then A, B, and C have a common prime factor."

Modelling choices: all variables are natural numbers with `0 < A, B, C` and `2 < x, y, z`;
"common prime factor" is a `Nat.Prime p` dividing each of `A, B, C`. No simplification. -/
def bealConjecture : Prop :=
  ∀ A B C x y z : ℕ, 0 < A → 0 < B → 0 < C → 2 < x → 2 < y → 2 < z →
    A ^ x + B ^ y = C ^ z → ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C

/-- **Known result (implication)** (Beal 1997, the conjecture was posed as a generalisation of
FLT): Beal's conjecture implies Fermat's Last Theorem for every exponent `n ≥ 3`. This is an
implication only (FLT itself is Wiles–Taylor's theorem, not formalised in Mathlib). -/
theorem beal_implies_FLT (hB : bealConjecture) : ∀ n ≥ 3, FermatLastTheoremFor n := by
  intro n hn
  rw [fermatLastTheoremFor_iff_nat]
  apply fermatLastTheoremWith_of_fermatLastTheoremWith_coprime
  intro a b c ha hb hc hg h
  obtain ⟨p, hp, hpa, hpb, hpc⟩ := hB a b c n n n (Nat.pos_of_ne_zero ha)
    (Nat.pos_of_ne_zero hb) (Nat.pos_of_ne_zero hc) hn hn hn h
  have : p ∣ ({a, b, c} : Finset ℕ).gcd id := by
    apply Finset.dvd_gcd
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  rw [hg] at this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **Known result** (Euler; Mathlib's `fermatLastTheoremThree`): the case `x = y = z = 3` of
Beal's conjecture, which holds because `A³ + B³ = C³` has no solution in positive integers. -/
theorem beal_exponent_three (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A ^ 3 + B ^ 3 = C ^ 3) : ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C :=
  absurd h (fermatLastTheoremThree A B C hA.ne' hB.ne' hC.ne')

/-- **Known result** (Fermat; Mathlib's `fermatLastTheoremFour`): the case `x = y = z = 4` of
Beal's conjecture, which holds because `A⁴ + B⁴ = C⁴` has no solution in positive integers. -/
theorem beal_exponent_four (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A ^ 4 + B ^ 4 = C ^ 4) : ∃ p : ℕ, p.Prime ∧ p ∣ A ∧ p ∣ B ∧ p ∣ C :=
  absurd h (fermatLastTheoremFour A B C hA.ne' hB.ne' hC.ne')

/-- **Finite check**: two Beal-type equalities with exponents `> 2`, `3³ + 6³ = 3⁵` and
`7³ + 7⁴ = 14³`; in each the bases share a prime factor (3, resp. 7), as the conjecture
predicts. Explicit identities only. -/
theorem beal_common_factor_examples :
    3 ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ 3 ∣ 3 ∧ 3 ∣ 6 ∧
      7 ^ 3 + 7 ^ 4 = 14 ^ 3 ∧ 7 ∣ 7 ∧ 7 ∣ 14 := by
  norm_num

/-- **Finite check**: `3² + 4² = 5²` with `3, 4, 5` pairwise coprime, so the hypothesis
"`x, y, z > 2`" in Beal's conjecture cannot be dropped. -/
theorem beal_needs_exponent_gt_two :
    3 ^ 2 + 4 ^ 2 = 5 ^ 2 ∧ ¬ ∃ p : ℕ, p.Prime ∧ p ∣ 3 ∧ p ∣ 4 ∧ p ∣ 5 := by
  refine ⟨by norm_num, ?_⟩
  rintro ⟨p, hp, h3, h4, -⟩
  have : p ∣ Nat.gcd 3 4 := Nat.dvd_gcd h3 h4
  norm_num at this
  exact hp.one_lt.ne' this

/-! ## Problem 344: the Fermat–Catalan conjecture -/

/-- The set of pairwise coprime positive triples `(x, y, z)` such that `x^p + y^q = z^r` for some
integers `p, q, r > 1` with `1/p + 1/q + 1/r < 1`. -/
def fermatCatalanSet : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧
    Nat.Coprime t.1 t.2.1 ∧ Nat.Coprime t.1 t.2.2 ∧ Nat.Coprime t.2.1 t.2.2 ∧
    ∃ p q r : ℕ, 1 < p ∧ 1 < q ∧ 1 < r ∧ (1 : ℚ) / p + 1 / q + 1 / r < 1 ∧
      t.1 ^ p + t.2.1 ^ q = t.2.2 ^ r}

/-- **Open problem (ProofAtlas rank 344, the Fermat–Catalan conjecture).**

ProofAtlas exactTarget: "Prove that there are only finitely many pairwise coprime
positive-integer triples (x,y,z) for which x^p + y^q = z^r for integers p,q,r > 1 satisfying
1/p + 1/q + 1/r < 1."

Modelling choices: exactly as quoted, finiteness of the set of *triples of bases*
`fermatCatalanSet ⊆ ℕ × ℕ × ℕ` (the exponents are existentially quantified per triple);
`1/p + 1/q + 1/r` is computed in `ℚ`. The more common formulation counts the *values*
`(x^p, y^q, z^r)`; the two differ, e.g., because `1 + 2³ = 3²` gives one triple `(1, 2, 3)`
but `1^p` for every `p`. -/
def fermatCatalanConjecture : Prop :=
  fermatCatalanSet.Finite

/-- **Finite check**: some of the ten known Fermat–Catalan solutions lie in
`fermatCatalanSet`: `1 + 2³ = 3²`, `2⁵ + 7² = 3⁴`, `7³ + 13² = 2⁹`, `2⁷ + 17³ = 71²`,
`3⁵ + 11⁴ = 122²`, and `33⁸ + 1549034² = 15613³` (Beukers–Zagier). Membership of explicit
triples only. -/
theorem fermatCatalan_known_solutions :
    (1, 2, 3) ∈ fermatCatalanSet ∧ (2, 7, 3) ∈ fermatCatalanSet ∧
      (7, 13, 2) ∈ fermatCatalanSet ∧ (2, 17, 71) ∈ fermatCatalanSet ∧
      (3, 11, 122) ∈ fermatCatalanSet ∧ (33, 1549034, 15613) ∈ fermatCatalanSet := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine ⟨by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, ?_⟩
  · exact ⟨7, 3, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 2, 4, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3, 2, 9, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7, 3, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, 4, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## Problem 372: sums of three cubes -/

/-- **Open problem (ProofAtlas rank 372, sums of three cubes, with Heath-Brown's refinement).**

ProofAtlas exactTarget: "Prove that every integer k not congruent to 4 or 5 modulo 9 admits a
representation k = x^3 + y^3 + z^3 in integers, with Heath-Brown's refinement asking for
infinitely many such representations for each eligible k."

Modelling choices: `k, x, y, z : ℤ`; `k % 9` is Lean's `Int.emod` (values in `0..8`), so
"not congruent to 4 or 5 mod 9" is `k % 9 ≠ 4 ∧ k % 9 ≠ 5`. The quoted target bundles two
statements; this Prop is the conjunction of the existence statement and Heath-Brown's
refinement (infinitely many ordered triples `(x, y, z)`). The refinement alone implies the
existence statement. See `sumsOfThreeCubesExistence` and `heathBrownThreeCubes`. -/
def sumsOfThreeCubesConjecture : Prop :=
  (∀ k : ℤ, k % 9 ≠ 4 → k % 9 ≠ 5 → ∃ x y z : ℤ, k = x ^ 3 + y ^ 3 + z ^ 3) ∧
    (∀ k : ℤ, k % 9 ≠ 4 → k % 9 ≠ 5 →
      {t : ℤ × ℤ × ℤ | k = t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3}.Infinite)

/-- First half of `sumsOfThreeCubesConjecture` (existence of one representation). -/
def sumsOfThreeCubesExistence : Prop :=
  ∀ k : ℤ, k % 9 ≠ 4 → k % 9 ≠ 5 → ∃ x y z : ℤ, k = x ^ 3 + y ^ 3 + z ^ 3

/-- Second half of `sumsOfThreeCubesConjecture` (Heath-Brown: infinitely many representations). -/
def heathBrownThreeCubes : Prop :=
  ∀ k : ℤ, k % 9 ≠ 4 → k % 9 ≠ 5 →
    {t : ℤ × ℤ × ℤ | k = t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3}.Infinite

theorem sumsOfThreeCubesConjecture_iff :
    sumsOfThreeCubesConjecture ↔ sumsOfThreeCubesExistence ∧ heathBrownThreeCubes :=
  Iff.rfl

/-- Heath-Brown's refinement implies the existence statement. -/
theorem heathBrown_implies_existence (h : heathBrownThreeCubes) : sumsOfThreeCubesExistence := by
  intro k h4 h5
  obtain ⟨t, ht⟩ := (h k h4 h5).nonempty
  exact ⟨t.1, t.2.1, t.2.2, ht⟩

/-- **Known result** (classical; cubes are `0, ±1 mod 9`): an integer `k ≡ 4` or `5 (mod 9)` is
not a sum of three integer cubes. This is why the conjecture excludes these classes. -/
theorem not_sum_three_cubes_of_mod_nine (k : ℤ) (hk : k % 9 = 4 ∨ k % 9 = 5) (x y z : ℤ) :
    k ≠ x ^ 3 + y ^ 3 + z ^ 3 := by
  intro h
  have hz : ((k % 9 : ℤ) : ZMod 9) = ((x ^ 3 + y ^ 3 + z ^ 3 : ℤ) : ZMod 9) := by
    have hm := ZMod.intCast_mod k 9
    push_cast at hm
    rw [hm, h]
  push_cast at hz
  have key : ∀ a b c : ZMod 9, a ^ 3 + b ^ 3 + c ^ 3 ≠ 4 ∧ a ^ 3 + b ^ 3 + c ^ 3 ≠ 5 := by
    decide
  rcases hk with hk | hk <;> rw [hk] at hz
  · exact (key x y z).1 (by rw [← hz]; rfl)
  · exact (key x y z).2 (by rw [← hz]; rfl)

/-- **Known result** (Mahler 1936): Heath-Brown's refinement holds for `k = 1`, via the identity
`(9t⁴)³ + (3t − 9t⁴)³ + (1 − 9t³)³ = 1`. -/
theorem threeCubes_infinite_one :
    {t : ℤ × ℤ × ℤ | (1 : ℤ) = t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℤ => (9 * t ^ 4, 3 * t - 9 * t ^ 4, 1 - 9 * t ^ 3)) ?_ ?_
  · intro s t hst
    simp only [Prod.mk.injEq] at hst
    have : s ^ 3 = t ^ 3 := by linarith [hst.2.2]
    exact (Odd.pow_injective (by decide : Odd 3)) this
  · intro t
    simp only [Set.mem_ofPred_eq]
    ring

/-- **Known result** (Werebrusow 1908): Heath-Brown's refinement holds for `k = 2`, via the
identity `(1 + 6t³)³ + (1 − 6t³)³ + (−6t²)³ = 2`. -/
theorem threeCubes_infinite_two :
    {t : ℤ × ℤ × ℤ | (2 : ℤ) = t.1 ^ 3 + t.2.1 ^ 3 + t.2.2 ^ 3}.Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun t : ℤ => (1 + 6 * t ^ 3, 1 - 6 * t ^ 3, -6 * t ^ 2)) ?_ ?_
  · intro s t hst
    simp only [Prod.mk.injEq] at hst
    have : s ^ 3 = t ^ 3 := by linarith [hst.1]
    exact (Odd.pow_injective (by decide : Odd 3)) this
  · intro t
    simp only [Set.mem_ofPred_eq]
    ring

/-- **Finite check**: every integer `0 ≤ k ≤ 20` with `k ≢ 4, 5 (mod 9)` is a sum of three
integer cubes (explicit witnesses). Says nothing about larger `k`. -/
theorem threeCubes_le_twenty (k : ℤ) (h0 : 0 ≤ k) (h20 : k ≤ 20) (h4 : k % 9 ≠ 4)
    (h5 : k % 9 ≠ 5) : ∃ x y z : ℤ, k = x ^ 3 + y ^ 3 + z ^ 3 := by
  interval_cases k <;> simp at h4 h5
  · exact ⟨0, 0, 0, by norm_num⟩
  · exact ⟨1, 0, 0, by norm_num⟩
  · exact ⟨1, 1, 0, by norm_num⟩
  · exact ⟨1, 1, 1, by norm_num⟩
  · exact ⟨2, -1, -1, by norm_num⟩
  · exact ⟨2, -1, 0, by norm_num⟩
  · exact ⟨2, 0, 0, by norm_num⟩
  · exact ⟨2, 1, 0, by norm_num⟩
  · exact ⟨2, 1, 1, by norm_num⟩
  · exact ⟨3, -2, -2, by norm_num⟩
  · exact ⟨7, 10, -11, by norm_num⟩
  · exact ⟨2, 2, -1, by norm_num⟩
  · exact ⟨2, 2, 0, by norm_num⟩
  · exact ⟨2, 2, 1, by norm_num⟩
  · exact ⟨3, -2, -1, by norm_num⟩
  · exact ⟨3, -2, 0, by norm_num⟩
  · exact ⟨3, -2, 1, by norm_num⟩

/-- **Finite check** (Booker 2019): an explicit representation of 33 as a sum of three cubes. -/
theorem threeCubes_thirtyThree :
    (33 : ℤ) = 8866128975287528 ^ 3 + (-8778405442862239) ^ 3 + (-2736111468807040) ^ 3 := by
  norm_num

/-- **Finite check** (Booker–Sutherland 2021): an explicit representation of 42 as a sum of
three cubes. -/
theorem threeCubes_fortyTwo :
    (42 : ℤ) = (-80538738812075974) ^ 3 + 80435758145817515 ^ 3 + 12602123297335631 ^ 3 := by
  norm_num

/-! ## Problem 395: Hall's conjecture -/

/-- **Open problem (ProofAtlas rank 395, Hall's conjecture, weak form with exponent
`1/2 − ε`).**

ProofAtlas exactTarget: "For every epsilon > 0, prove that there is c(epsilon) > 0 such that all
positive integers x and y with y^2 != x^3 satisfy |y^2-x^3| > c(epsilon) x^(1/2-epsilon)."

Modelling choices: `x, y : ℕ` positive, `ε, c : ℝ`, `x^(1/2 − ε)` is `Real.rpow` and
`|y² − x³|` is computed in `ℝ`. No simplification. -/
def hallConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ x y : ℕ, 0 < x → 0 < y → y ^ 2 ≠ x ^ 3 →
    c * (x : ℝ) ^ ((1 : ℝ) / 2 - ε) < |(y : ℝ) ^ 2 - (x : ℝ) ^ 3|

/-- **Finite check** (Hall's example, cited in Danilov 1982 / Elkies 2000 tables):
`378661² − 5234³ = 17`, a small difference relative to `√5234 ≈ 72.3`. One explicit pair. -/
theorem hall_example_5234 : (378661 : ℤ) ^ 2 - 5234 ^ 3 = 17 := by norm_num

/-! ## Problem 493: Pillai's conjecture -/

/-- `n` is a perfect power `x^a` with `x ≥ 1` and `a ≥ 2` (so `1 = 1²` counts). -/
def IsPerfectPowerPos (n : ℕ) : Prop :=
  ∃ x a : ℕ, 0 < x ∧ 2 ≤ a ∧ x ^ a = n

/-- Pairs `(x^a, y^b)` of perfect powers (as values) with `x^a − y^b = k`. -/
def pillaiSet (k : ℕ) : Set (ℕ × ℕ) :=
  {p | IsPerfectPowerPos p.1 ∧ IsPerfectPowerPos p.2 ∧ p.1 = p.2 + k}

/-- **Open problem (ProofAtlas rank 493, Pillai's conjecture).**

ProofAtlas exactTarget: "Prove or disprove that for every fixed integer k >= 1 there are only
finitely many pairs of perfect powers x^a and y^b (with a,b >= 2) whose difference equals k."

Modelling choices: bases `x, y` are positive integers and exponents `a, b ≥ 2`; a "pair of
perfect powers" is the pair of *values* `(x^a, y^b) ∈ ℕ × ℕ` (as in the quote); "difference
equals k" is read as `x^a − y^b = k` (the order is immaterial for finiteness, since swapping
gives `y^b − x^a = −k` with `k > 0` impossible). The ProofAtlas wording is "prove or disprove";
this Prop is the affirmative (conjectured) direction. -/
def pillaiConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → (pillaiSet k).Finite

/-- **Finite check**: `(9, 8) = (3², 2³)` lies in `pillaiSet 1` (Catalan's solution). -/
theorem pillai_catalan_example : ((9, 8) : ℕ × ℕ) ∈ pillaiSet 1 :=
  ⟨⟨3, 2, by norm_num, le_rfl, by norm_num⟩, ⟨2, 3, by norm_num, by norm_num, by norm_num⟩,
    by norm_num⟩

/-- **Known result** (elementary, factor `x² − y² = (x − y)(x + y)`): for `k ≥ 1` there are only
finitely many pairs `(x, y)` of naturals with `x² = y² + k` (the case `a = b = 2` of Pillai's
equation). -/
theorem pillai_squares_finite (k : ℕ) (hk : 1 ≤ k) :
    {p : ℕ × ℕ | p.1 ^ 2 = p.2 ^ 2 + k}.Finite := by
  apply (Set.finite_Iic ((k, k) : ℕ × ℕ)).subset
  rintro ⟨x, y⟩ h
  simp only [Set.mem_ofPred_eq] at h
  have hxy : y < x := by
    by_contra hh
    push Not at hh
    have : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hh 2
    omega
  have hxk : x ≤ k := by nlinarith
  exact ⟨hxk, by simp only; omega⟩

/-! ## Axiom checks -/

#print axioms masonStothers
#print axioms abc_reyssat_triple
#print axioms abc_implies_eventually_FLT
#print axioms beal_implies_FLT
#print axioms beal_exponent_three
#print axioms beal_exponent_four
#print axioms beal_common_factor_examples
#print axioms beal_needs_exponent_gt_two
#print axioms fermatCatalan_known_solutions
#print axioms sumsOfThreeCubesConjecture_iff
#print axioms heathBrown_implies_existence
#print axioms not_sum_three_cubes_of_mod_nine
#print axioms threeCubes_infinite_one
#print axioms threeCubes_infinite_two
#print axioms threeCubes_le_twenty
#print axioms threeCubes_thirtyThree
#print axioms threeCubes_fortyTwo
#print axioms hall_example_5234
#print axioms pillai_catalan_example
#print axioms pillai_squares_finite

end CryptoLean.OpenProblems.NumberTheory.Diophantine
