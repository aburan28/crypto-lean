import Mathlib

/-!
# Special primes and perfect numbers: Artin, odd perfect numbers, Mersenne and Fermat primes

ProofAtlas problems (by `releaseRank`):
* #182 Artin's primitive root conjecture      → `ArtinPrimitiveRootConjecture`
* #214 Existence of an odd perfect number      → `OddPerfectNumberExists`
* #227 Infinitude of Mersenne primes           → `InfinitelyManyMersennePrimes`
* #402 Infinitude of Fermat primes             → `InfinitelyManyFermatPrimes`

**All four problems are open.**  Each appears below only as an unproved `def … : Prop` whose
docstring quotes the ProofAtlas `exactTarget` and lists the modelling choices.  Nothing in this
file proves, refutes, or is evidence towards any of them.  (#214 and #402 ask to *determine
whether*; the `Prop` is the existence / infinitude statement and the open problem is to decide
it.  #182 and #227 say "prove or disprove"; the `Prop` is the conjectured direction.)

What *is* proved here:
* **Bridges** (equivalences between formulations, not progress):
  `oddPerfectNumberExists_iff` (Mathlib `Nat.Perfect`),
  `infinitelyManyMersennePrimes_iff_mersenne`, `infinitelyManyMersennePrimes_iff_evenPerfect`
  (the ProofAtlas "equivalently, infinitely many even perfect numbers"),
  `infinitelyManyFermatPrimes_iff_fermatNumber` (Mathlib `Nat.fermatNumber`),
  `infinitelyManyFermatPrimes_iff_primes_two_pow_add_one`.
* **Known results:**
  - `prime_of_two_pow_sub_one_prime`: `2^n - 1` prime ⇒ `n` prime.
  - `exists_eq_two_pow_of_two_pow_add_one_prime`: `2^n + 1` prime, `n ≠ 0` ⇒ `n` a power of 2.
  - `fermatNumber_five_eq`, `not_prime_fermatNumber_five`: Euler's factorisation
    `F₅ = 641 · 6700417`.
  - `even_and_perfect_iff`: the Euclid–Euler theorem.  It is in Mathlib's `Archive`
    (`Theorems100.Nat.even_and_perfect_iff`), which `import Mathlib` does not provide, so the
    Archive proof is ported here with attribution.
  - `not_perfect_of_isPrimePow`: no prime power is perfect.
  - `euler_form`: an odd perfect number has the form `p^k m²`, `p ≡ k ≡ 1 (mod 4)`, `p ∤ m`.
  - `square_not_primitiveRoot`, `neg_one_not_primitiveRoot`: why Artin excludes squares and `-1`.
* **Finite checks** (say nothing about the infinite statements):
  `two_isPrimitiveRoot_mod_{3,5,11,13}`, `two_not_primitiveRoot_mod_seven`,
  `mersenne_prime_exponents_small` (`2^p - 1` prime for `p = 2,3,5,7,13`),
  `fermat_primes_small` (`F₀, …, F₄` prime).

Missing from Mathlib (noted, not worked around): Artin's constant and Hooley's GRH-conditional
theorem; the Chebotarev density theorem in the form needed to evaluate the Artin density series `∑ artinTerm a`.  We state
#182 with the density written as the Kummer-degree series, see `ArtinPrimitiveRootConjecture`.
-/

namespace CryptoLean.OpenProblems.NumberTheory.SpecialPrimes

open ArithmeticFunction Finset Filter Topology
open scoped ArithmeticFunction.sigma

/-! ## #182 Artin's primitive root conjecture -/

open Polynomial in
/-- `[ℚ(ζₙ, a^{1/n}) : ℚ]`, written as the degree over `ℚ` of the splitting field of `Xⁿ - a`.
For `n ≥ 1` and `a ≠ 0` the splitting field of `Xⁿ - a` over `ℚ` is exactly `ℚ(ζₙ, a^{1/n})`
(its roots are `ζₙ^i α`, whose ratios generate `μₙ`). -/
noncomputable def kummerDegree (a : ℤ) (n : ℕ) : ℕ :=
  Module.finrank ℚ (SplittingField (X ^ n - C (a : ℚ) : ℚ[X]))

/-- The `(n+1)`-st term `μ(n+1) / [ℚ(ζ_{n+1}, a^{1/(n+1)}) : ℚ]` of the Artin density series
(indexed from `0` so that it runs over `n + 1 ≥ 1`). -/
noncomputable def artinTerm (a : ℤ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (n + 1) : ℝ) / (kummerDegree a (n + 1) : ℝ)

open Classical in
/-- Number of primes `p ≤ x` for which `a` is a primitive root modulo `p`, i.e. the class of `a`
in `ZMod p` has multiplicative order `p - 1`.  (If `p ∣ a` the class is `0`, of order `0 ≠ p - 1`,
so such `p` are not counted.) -/
noncomputable def primitiveRootPrimeCount (a : ℤ) (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ orderOf ((a : ZMod p)) = p - 1)).card

/-- **Artin's primitive root conjecture** (ProofAtlas #182, OPEN).

ProofAtlas exactTarget: "Prove or disprove that every integer a other than -1 that is not a
perfect square is a primitive root modulo p for a positive natural density of primes p, with the
density given by Artin's predicted correction factor."

Modelling:
* `a : ℤ`, `a ≠ -1`, `¬ IsSquare a` (so also `a ≠ 0, 1`).
* "primitive root modulo `p`": `orderOf (a : ZMod p) = p - 1` (`primitiveRootPrimeCount`).
* "natural density of primes": the relative density among primes, i.e. the limit of
  `#{p ≤ x : a prim. root mod p} / π(x)` as `x → ∞` along `ℕ` (`Nat.primeCounting`).
* "Artin's predicted density with correction factor": we use the corrected (Heilbronn /
  Lehmer–Lehmer, proved under GRH by Hooley 1967) form
  `δ(a) = ∑_{n ≥ 1} μ(n) / [ℚ(ζₙ, a^{1/n}) : ℚ]`, which equals Artin's constant times the
  rational correction factor depending on `a` (its `h`-th power structure and the
  discriminant of `ℚ(√a)`).  The degree is `kummerDegree` (splitting field of `Xⁿ - a`).
  The series is required to converge unconditionally in `ℝ` (`HasSum`, i.e. absolutely);
  it does, since `[ℚ(ζₙ, a^{1/n}) : ℚ] ≫_a n φ(n)`.
* "positive": the Prop asserts `0 < δ(a)`.
* "Prove or disprove": the `Prop` is the "prove" direction. -/
def ArtinPrimitiveRootConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    ∃ δ : ℝ, HasSum (artinTerm a) δ ∧ 0 < δ ∧
      Tendsto (fun x : ℕ => (primitiveRootPrimeCount a x : ℝ) / (Nat.primeCounting x : ℝ))
        atTop (𝓝 δ)

/-- **Known result** (elementary; Gauss, *Disquisitiones* art. 97–98): a perfect square `b²` is a
primitive root modulo no odd prime `p` (it is a quadratic residue, or `0`, so its order divides
`(p-1)/2`).  This is why Artin's conjecture excludes squares. -/
theorem square_not_primitiveRoot (b : ℤ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    orderOf (((b ^ 2 : ℤ) : ZMod p)) ≠ p - 1 := by
  have := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpo : Odd p := hp.odd_of_ne_two hp2
  intro h
  push_cast at h
  by_cases hb : (b : ZMod p) = 0
  · rw [hb, zero_pow two_ne_zero, orderOf_eq_zero_iff'.mpr] at h
    · omega
    · intro n hn; simp [zero_pow hn.ne']
  · have hfermat : ((b : ZMod p) ^ 2) ^ ((p - 1) / 2) = 1 := by
      obtain ⟨k, hk⟩ := hpo
      rw [← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hb
    have := orderOf_le_of_pow_eq_one (by omega) hfermat
    omega

/-- **Known result** (elementary): `-1` has order at most `2`, so it is a primitive root modulo
no prime `p > 3`.  This is why Artin's conjecture excludes `a = -1`. -/
theorem neg_one_not_primitiveRoot {p : ℕ} (hp3 : 3 < p) :
    orderOf (((-1 : ℤ) : ZMod p)) ≠ p - 1 := by
  intro h
  have : ((-1 : ℤ) : ZMod p) ^ 2 = 1 := by push_cast; ring
  have := orderOf_le_of_pow_eq_one (by omega) this
  omega

/-- **Finite check** (not evidence for Artin's conjecture): `2` is a primitive root mod `3`. -/
theorem two_isPrimitiveRoot_mod_three : orderOf ((2 : ℤ) : ZMod 3) = 3 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- **Finite check**: `2` is a primitive root mod `5`. -/
theorem two_isPrimitiveRoot_mod_five : orderOf ((2 : ℤ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- **Finite check**: `2` is a primitive root mod `11`. -/
theorem two_isPrimitiveRoot_mod_eleven : orderOf ((2 : ℤ) : ZMod 11) = 11 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- **Finite check**: `2` is a primitive root mod `13`. -/
theorem two_isPrimitiveRoot_mod_thirteen : orderOf ((2 : ℤ) : ZMod 13) = 13 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]; decide

/-- **Finite check**: `2` is *not* a primitive root mod `7` (`2³ = 8 ≡ 1`). -/
theorem two_not_primitiveRoot_mod_seven : orderOf ((2 : ℤ) : ZMod 7) ≠ 7 - 1 := by
  have h : ((2 : ℤ) : ZMod 7) ^ 3 = 1 := by decide
  have := orderOf_le_of_pow_eq_one (by norm_num) h
  omega

/-! ## #214 Odd perfect numbers -/

/-- **Existence of an odd perfect number** (ProofAtlas #214, OPEN).

ProofAtlas exactTarget: "Determine whether there exists an odd positive integer N satisfying
sigma(N)=2N, where sigma is the sum-of-positive-divisors function; equivalently, prove that every
perfect number is even or construct an odd perfect number."

Modelling: `N : ℕ`, `σ(N) = ∑_{d ∣ N} d` via `Nat.divisors`.  The `Prop` is the existence
statement; the open problem is to decide whether it holds.  Equivalent to Mathlib's
`∃ n, Odd n ∧ Nat.Perfect n` (`oddPerfectNumberExists_iff`). -/
def OddPerfectNumberExists : Prop :=
  ∃ N : ℕ, Odd N ∧ 0 < N ∧ ∑ d ∈ N.divisors, d = 2 * N

/-- Bridge: the quoted statement agrees with Mathlib's `Nat.Perfect`. -/
theorem oddPerfectNumberExists_iff : OddPerfectNumberExists ↔ ∃ n : ℕ, Odd n ∧ n.Perfect := by
  constructor
  · rintro ⟨N, ho, hp, hs⟩
    exact ⟨N, ho, (Nat.perfect_iff_sum_divisors_eq_two_mul hp).2 hs⟩
  · rintro ⟨N, ho, hN⟩
    exact ⟨N, ho, hN.2, (Nat.perfect_iff_sum_divisors_eq_two_mul hN.2).1 hN⟩

/-- **Known result** (elementary; e.g. Dickson, *History* I, Ch. I): no prime power is perfect
(prime powers are deficient: `σ(p^k) < 2 p^k`, Mathlib `IsPrimePow.deficient`).  In particular an
odd perfect number, if one exists, is not a prime power. -/
theorem not_perfect_of_isPrimePow {n : ℕ} (h : IsPrimePow n) : ¬ n.Perfect := by
  intro hp
  have hd := h.deficient
  exact absurd hd ((Nat.perfect_iff_not_abundant_and_not_deficient
    (Nat.pos_of_ne_zero h.ne_zero).ne).1 hp).2

/-- Elementary lemma: if `q ≡ 1 (mod 4)` then `1 + q + ⋯ + q^(n-1) ≡ n (mod 4)`. -/
theorem geom_mod_four_of_one (q n : ℕ) (hq : q % 4 = 1) :
    (∑ i ∈ range n, q ^ i) % 4 = n % 4 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hq, one_pow]
    omega

/-- Elementary lemma: if `q ≡ 3 (mod 4)` then `1 + q + ⋯ + q^(2j-1) ≡ 0 (mod 4)`. -/
theorem geom_mod_four_of_three (q j : ℕ) (hq : q % 4 = 3) :
    (∑ i ∈ range (2 * j), q ^ i) % 4 = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : q ^ (2 * j) % 4 = 1 := by
      have hsq : q ^ 2 % 4 = 1 := by rw [sq, Nat.mul_mod, hq]
      rw [pow_mul, Nat.pow_mod, hsq, one_pow, Nat.one_mod]
    have h2 : q ^ (2 * j + 1) % 4 = 3 := by
      rw [pow_succ, Nat.mul_mod, h1, hq]
    rw [show 2 * (j+1) = 2 * j + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    omega

/-- Elementary lemma: if `q` is odd then `1 + q + ⋯ + q^(n-1) ≡ n (mod 2)`. -/
theorem geom_mod_two_of_odd (q n : ℕ) (hq : q % 2 = 1) :
    (∑ i ∈ range n, q ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hq, one_pow]
    omega

/-- **Known result (Euler's form of an odd perfect number).** If `N` is an odd perfect number
then `N = p^k m²` with `p` prime, `p ≡ k ≡ 1 (mod 4)` and `p ∤ m`.
Citation: L. Euler, *De numeris amicabilibus* (1747, publ. 1849); see e.g. Dickson,
*History of the Theory of Numbers* I, Ch. I.  This is a constraint on a hypothetical odd perfect
number; it does **not** decide whether one exists (problem #214 remains open). -/
theorem euler_form {N : ℕ} (hodd : Odd N) (hperf : N.Perfect) :
    ∃ p k m : ℕ, p.Prime ∧ p % 4 = 1 ∧ k % 4 = 1 ∧ ¬ p ∣ m ∧ N = p ^ k * m ^ 2 := by
  have hN0 : N ≠ 0 := hperf.2.ne'
  have hσ : σ 1 N = 2 * N := by
    rw [sigma_one_apply]; exact (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).1 hperf
  set e := N.factorization with he
  set f : ℕ → ℕ := fun p => σ 1 (p ^ e p) with hf
  have hprod : σ 1 N = ∏ p ∈ N.primeFactors, f p := by
    rw [isMultiplicative_sigma.multiplicative_factorization _ hN0, Finsupp.prod,
      Nat.support_factorization]
  have hpodd : ∀ p ∈ N.primeFactors, p % 2 = 1 := by
    intro p hp
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have : ¬ 2 ∣ p := fun h2 => by
      have := Nat.odd_iff.mp hodd
      have : 2 ∣ N := h2.trans hpN
      omega
    omega
  have hgeom : ∀ p ∈ N.primeFactors, f p = ∑ i ∈ range (e p + 1), p ^ i := by
    intro p hp
    simp only [hf]
    rw [sigma_one_apply_prime_pow (Nat.prime_of_mem_primeFactors hp)]
  have hfpar : ∀ p ∈ N.primeFactors, (2 ∣ f p ↔ Odd (e p)) := by
    intro p hp
    have := geom_mod_two_of_odd p (e p + 1) (hpodd p hp)
    rw [← hgeom p hp] at this
    rw [Nat.odd_iff]; omega
  have hN2 : ¬ 2 ∣ N := by have := Nat.odd_iff.mp hodd; omega
  have h4 : ¬ 4 ∣ σ 1 N := by
    rw [hσ]; intro h; exact hN2 (by omega)
  set S := N.primeFactors.filter (fun p => Odd (e p)) with hS
  set T := N.primeFactors.filter (fun p => ¬ Odd (e p)) with hT
  have hsplit : σ 1 N = (∏ p ∈ S, f p) * ∏ p ∈ T, f p := by
    rw [hprod, prod_filter_mul_prod_filter_not]
  have hTodd : ¬ 2 ∣ ∏ p ∈ T, f p := by
    rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime]
    rintro ⟨p, hpT, h2⟩
    rw [hT, mem_filter] at hpT
    exact hpT.2 ((hfpar p hpT.1).1 h2)
  -- `S` is a singleton
  have hScard : S.card = 1 := by
    rcases Nat.lt_or_ge S.card 2 with h | h
    · rcases Nat.lt_or_ge S.card 1 with h' | h'
      · have hSe : S = ∅ := card_eq_zero.mp (by omega)
        apply absurd _ hTodd
        have : 2 ∣ σ 1 N := by rw [hσ]; exact dvd_mul_right 2 N
        rwa [hsplit, hSe, prod_empty, one_mul] at this
      · omega
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (by omega : 1 < S.card)
      apply h4
      rw [hsplit]
      apply Dvd.dvd.mul_right
      have hsub : ({a, b} : Finset ℕ) ⊆ S := by
        intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
      refine dvd_trans ?_ (prod_dvd_prod_of_subset _ _ f hsub)
      rw [prod_pair hab, show (4 : ℕ) = 2 * 2 by rfl]
      rw [hS, mem_filter] at ha hb
      exact mul_dvd_mul ((hfpar a ha.1).2 ha.2) ((hfpar b hb.1).2 hb.2)
  obtain ⟨p, hSp⟩ := card_eq_one.mp hScard
  have hpS : p ∈ S := by rw [hSp]; exact mem_singleton_self p
  rw [hS, mem_filter] at hpS
  obtain ⟨hpN, hep⟩ := hpS
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpN
  have hf4 : ¬ 4 ∣ f p := by
    intro h; apply h4; rw [hsplit, hSp, prod_singleton]; exact Dvd.dvd.mul_right h _
  have hp4 : p % 4 = 1 := by
    have h2 := hpodd p hpN
    rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
    · exact h
    · exfalso; apply hf4
      obtain ⟨j, hj⟩ := hep
      have := geom_mod_four_of_three p (j + 1) h
      rw [hgeom p hpN, show e p + 1 = 2 * (j + 1) by omega]
      omega
  have hk4 : e p % 4 = 1 := by
    have := geom_mod_four_of_one p (e p + 1) hp4
    rw [← hgeom p hpN] at this
    have : ¬ (f p % 4 = 0) := fun h => hf4 (Nat.dvd_of_mod_eq_zero h)
    have := Nat.odd_iff.mp hep
    omega
  -- the square part
  have heven : ∀ q ∈ N.primeFactors.erase p, Even (e q) := by
    intro q hq
    obtain ⟨hqp, hq⟩ := mem_erase.mp hq
    by_contra hne
    rw [Nat.not_even_iff_odd] at hne
    have : q ∈ S := by rw [hS, mem_filter]; exact ⟨hq, hne⟩
    rw [hSp, mem_singleton] at this
    exact hqp this
  refine ⟨p, e p, ∏ q ∈ N.primeFactors.erase p, q ^ (e q / 2), hp, hp4, hk4, ?_, ?_⟩
  · rw [Prime.dvd_finsetProd_iff hp.prime]
    rintro ⟨q, hq, hdvd⟩
    obtain ⟨hqp, hq⟩ := mem_erase.mp hq
    have := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hq)).1
      (hp.dvd_of_dvd_pow hdvd)
    exact hqp this.symm
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization, ← mul_prod_erase _ _ hpN, ← prod_pow]
    congr 1
    refine prod_congr rfl fun q hq => ?_
    rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp (heven q hq))]

/-! ### Euclid–Euler theorem (ported from Mathlib's Archive) -/

/-- `σ(2^k) = 2^(k+1) - 1`.  (Ported from Mathlib `Archive/Wiedijk100Theorems/PerfectNumbers.lean`,
which is not part of `import Mathlib`.) -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- **Known result (Euclid, *Elements* IX.36).** If `2^(k+1) - 1` is prime then
`2^k (2^(k+1) - 1)` is perfect.  Proof ported from Mathlib's Archive (Theorems100). -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

/-- The Euclid number `2^k (2^(k+1) - 1)` attached to a Mersenne prime is even. -/
theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  have hk : k ≠ 0 := by rintro rfl; simp [mersenne, Nat.not_prime_one] at pr
  simp [hk, parity_simps]

/-- **Known result (Euler, 1747/1849).** Every even perfect number is `2^k (2^(k+1) - 1)` with
`2^(k+1) - 1` prime.  Proof ported from Mathlib's Archive (Theorems100). -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  obtain ⟨k, m, hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hm : ¬ Even m := Nat.not_even_iff_odd.mpr hm'
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
    rw [← one_mul j, ← mul_assoc, mul_one] at jcon
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-- **Known result (Euclid–Euler theorem).** `n` is an even perfect number iff
`n = 2^k (2^(k+1) - 1)` with `2^(k+1) - 1` prime.  Citation: Euclid IX.36; Euler (1849);
Mathlib Archive `Theorems100.Nat.even_and_perfect_iff` (ported here). -/
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  constructor
  · rintro ⟨ev, perf⟩
    exact eq_two_pow_mul_prime_mersenne_of_even_perfect ev perf
  · rintro ⟨k, pr, rfl⟩
    exact ⟨even_two_pow_mul_mersenne_of_prime k pr, perfect_two_pow_mul_mersenne_of_prime k pr⟩

/-! ## #227 Mersenne primes -/

/-- **Infinitude of Mersenne primes** (ProofAtlas #227, OPEN).

ProofAtlas exactTarget: "Prove or disprove that there are infinitely many primes p for which the
Mersenne number 2^p - 1 is prime. Equivalently (by the Euclid-Euler theorem), prove or disprove
that there are infinitely many even perfect numbers."

Modelling: `p : ℕ`, natural subtraction `2^p - 1` (no truncation since `2^p ≥ 1`), `Set.Infinite`.
The `Prop` is the "prove" direction.  Both quoted equivalents are proved equivalent below
(`infinitelyManyMersennePrimes_iff_mersenne`, `infinitelyManyMersennePrimes_iff_evenPerfect`). -/
def InfinitelyManyMersennePrimes : Prop :=
  {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime}.Infinite

/-- **Known result** (Cataldi/Fermat; elementary): if `2^n - 1` is prime then `n` is prime.
Mathlib `Nat.Prime.of_mersenne`. -/
theorem prime_of_two_pow_sub_one_prime {n : ℕ} (h : (2 ^ n - 1).Prime) : n.Prime :=
  Nat.Prime.of_mersenne h

/-- **Finite check**: `2^p - 1` is prime for `p = 2, 3, 5, 7, 13`.  Not evidence for #227. -/
theorem mersenne_prime_exponents_small :
    (2 ^ 2 - 1).Prime ∧ (2 ^ 3 - 1).Prime ∧ (2 ^ 5 - 1).Prime ∧ (2 ^ 7 - 1).Prime ∧
      (2 ^ 13 - 1).Prime := by
  norm_num

/-- Bridge: the quoted set equals `{p | mersenne p prime}` (since `2^p - 1` prime forces `p` prime,
Mathlib `Nat.Prime.of_mersenne`). -/
theorem mersenne_set_eq : {p : ℕ | p.Prime ∧ (2 ^ p - 1).Prime} = {p : ℕ | (mersenne p).Prime} := by
  ext p
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨Nat.Prime.of_mersenne h, h⟩⟩

/-- Bridge: reindexing `p = k + 1` (note `mersenne 0 = 0` is not prime). -/
theorem mersenne_set_eq_image :
    {p : ℕ | (mersenne p).Prime} = (· + 1) '' {k : ℕ | (mersenne (k + 1)).Prime} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    rcases p with _ | k
    · simp [mersenne, Nat.not_prime_zero] at h
    · exact ⟨k, h, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact hk

/-- Bridge (via Euclid–Euler): the even perfect numbers are the image of the Mersenne-prime
exponents under `k ↦ 2^k (2^(k+1) - 1)`. -/
theorem evenPerfect_set_eq :
    {n : ℕ | Even n ∧ n.Perfect} =
      (fun k => 2 ^ k * mersenne (k + 1)) '' {k : ℕ | (mersenne (k + 1)).Prime} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_image, even_and_perfect_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩

/-- `k ↦ 2^k (2^(k+1) - 1)` is strictly increasing. -/
theorem strictMono_evenPerfect : StrictMono (fun k : ℕ => 2 ^ k * mersenne (k + 1)) := by
  intro a b hab
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : mersenne (a + 1) < mersenne (b + 1) := strictMono_mersenne (by omega)
  exact Nat.mul_lt_mul'' h1 h2

/-- Bridge: `InfinitelyManyMersennePrimes` is equivalent to the statement phrased with Mathlib's
`mersenne`. -/
theorem infinitelyManyMersennePrimes_iff_mersenne :
    InfinitelyManyMersennePrimes ↔ {p : ℕ | (mersenne p).Prime}.Infinite := by
  rw [InfinitelyManyMersennePrimes, mersenne_set_eq]

/-- Bridge: the equivalence quoted in the ProofAtlas target — infinitely many Mersenne primes iff
infinitely many even perfect numbers (via the Euclid–Euler theorem).  An equivalence of two open
statements, not progress on either. -/
theorem infinitelyManyMersennePrimes_iff_evenPerfect :
    InfinitelyManyMersennePrimes ↔ {n : ℕ | Even n ∧ n.Perfect}.Infinite := by
  rw [infinitelyManyMersennePrimes_iff_mersenne, mersenne_set_eq_image, evenPerfect_set_eq,
    Set.infinite_image_iff (add_left_injective 1).injOn,
    Set.infinite_image_iff strictMono_evenPerfect.injective.injOn]

/-! ## #402 Fermat primes -/

/-- **Infinitude of Fermat primes** (ProofAtlas #402, OPEN).

ProofAtlas exactTarget: "Determine whether infinitely many Fermat numbers F_n=2^(2^n)+1 are prime;
equivalently, prove that the set of n≥0 with F_n prime is infinite or prove that it is finite."

Modelling: `n : ℕ` (so `n ≥ 0`), `Set.Infinite`.  The `Prop` is the infinitude statement; the
open problem is to decide it (its negation is "the set is finite"). -/
def InfinitelyManyFermatPrimes : Prop :=
  {n : ℕ | (2 ^ (2 ^ n) + 1).Prime}.Infinite

/-- **Known result** (Fermat/Euler; elementary): if `2^n + 1` is prime and `n ≠ 0` then `n` is a
power of `2`.  Mathlib `Nat.pow_of_pow_add_prime`. -/
theorem exists_eq_two_pow_of_two_pow_add_one_prime {n : ℕ} (hn : n ≠ 0)
    (h : (2 ^ n + 1).Prime) : ∃ m : ℕ, n = 2 ^ m :=
  Nat.pow_of_pow_add_prime one_lt_two hn h

/-- **Known result** (Euler, 1732): `F₅ = 2^32 + 1 = 641 · 6700417`. -/
theorem fermatNumber_five_eq : Nat.fermatNumber 5 = 641 * 6700417 := by
  rw [Nat.fermatNumber]; norm_num

/-- **Known result** (Euler, 1732): `F₅` is composite; `641 ∣ F₅`. -/
theorem not_prime_fermatNumber_five : 641 ∣ Nat.fermatNumber 5 ∧ ¬ (Nat.fermatNumber 5).Prime := by
  rw [fermatNumber_five_eq]
  exact ⟨dvd_mul_right _ _, Nat.not_prime_mul (by norm_num) (by norm_num)⟩

/-- **Finite check**: `F₀, …, F₄` (3, 5, 17, 257, 65537) are prime.  Not evidence for #402. -/
theorem fermat_primes_small :
    ∀ n < 5, (Nat.fermatNumber n).Prime := by
  intro n hn
  interval_cases n <;> norm_num [Nat.fermatNumber]

/-- Bridge: the quoted statement agrees definitionally with Mathlib's `Nat.fermatNumber`. -/
theorem infinitelyManyFermatPrimes_iff_fermatNumber :
    InfinitelyManyFermatPrimes ↔ {n : ℕ | (Nat.fermatNumber n).Prime}.Infinite := Iff.rfl

/-- Bridge: the primes of the form `2^m + 1` are `2` together with the Fermat primes (uses the
known result that `2^m + 1` prime with `m ≠ 0` forces `m = 2^n`, Mathlib
`Nat.pow_of_pow_add_prime`). -/
theorem primes_two_pow_add_one_eq :
    {q : ℕ | q.Prime ∧ ∃ m, q = 2 ^ m + 1} =
      insert 2 (Nat.fermatNumber '' {n : ℕ | (Nat.fermatNumber n).Prime}) := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image]
  constructor
  · rintro ⟨hq, m, rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left; rfl
    · right
      obtain ⟨n, rfl⟩ := Nat.pow_of_pow_add_prime one_lt_two hm.ne' hq
      exact ⟨n, hq, rfl⟩
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨Nat.prime_two, 0, rfl⟩
    · exact ⟨hn, 2 ^ n, rfl⟩

/-- Bridge: infinitely many Fermat primes iff infinitely many primes of the form `2^m + 1`.
An equivalence of two forms of the open statement, not progress. -/
theorem infinitelyManyFermatPrimes_iff_primes_two_pow_add_one :
    InfinitelyManyFermatPrimes ↔ {q : ℕ | q.Prime ∧ ∃ m, q = 2 ^ m + 1}.Infinite := by
  rw [primes_two_pow_add_one_eq, Set.Infinite, Set.finite_insert, ← Set.Infinite,
    Set.infinite_image_iff Nat.fermatNumber_injective.injOn]
  rfl

end CryptoLean.OpenProblems.NumberTheory.SpecialPrimes

#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.square_not_primitiveRoot
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.neg_one_not_primitiveRoot
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.two_isPrimitiveRoot_mod_thirteen
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.two_not_primitiveRoot_mod_seven
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.oddPerfectNumberExists_iff
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.not_perfect_of_isPrimePow
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.euler_form
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.even_and_perfect_iff
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.prime_of_two_pow_sub_one_prime
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.mersenne_prime_exponents_small
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.infinitelyManyMersennePrimes_iff_mersenne
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.infinitelyManyMersennePrimes_iff_evenPerfect
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.exists_eq_two_pow_of_two_pow_add_one_prime
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.not_prime_fermatNumber_five
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.fermat_primes_small
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.infinitelyManyFermatPrimes_iff_fermatNumber
#print axioms CryptoLean.OpenProblems.NumberTheory.SpecialPrimes.infinitelyManyFermatPrimes_iff_primes_two_pow_add_one
