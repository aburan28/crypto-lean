import Mathlib

/-!
# Prime gaps and additive problems: Goldbach, Elliott–Halberstam, Cramér, Legendre, Oppermann

ProofAtlas problems (by `releaseRank`):
* #24  Binary Goldbach problem                    → `BinaryGoldbachConjecture`
* #83  Elliott–Halberstam conjecture              → `ElliottHalberstamConjecture`
* #148 Cramér's conjecture (limsup of gaps)       → `CramerConjecture`
* #275 Legendre's conjecture                      → `LegendreConjecture`
* #445 Oppermann's conjecture                     → `OppermannConjecture`

**All five problems are open.**  (ProofAtlas lists #445 as `open_disputed_claim`: there are
published claims of a proof that are not accepted; it is treated as open here.)  Each appears
below only as an unproved `def … : Prop` whose docstring quotes the ProofAtlas `exactTarget`
and lists the modelling choices.  Nothing in this file proves, or is evidence towards, any of
them.

What *is* proved here:
* **Known results.**
  - `bertrand_postulate`: Bertrand's postulate (Mathlib `Nat.bertrand`).
  - `exists_prime_strict_between_two_mul`: for `n ≥ 2` there is a prime `p` with
    `n < p < 2n` (consequence of Bertrand, since `2n` is not prime).
* **Implications between statements** (logical reductions, not progress):
  - `oppermann_implies_legendre`.
  - `legendre_implies_prime_gap_bound`: Legendre's conjecture implies that every interval
    `(x, x + 4·⌊√x⌋ + 4)` contains a prime, i.e. prime gaps are `O(√p)`.
* **Finite checks** (bounded ranges; these say nothing about the infinite statements):
  - `goldbach_upto_1000`: every even `n` with `4 ≤ n ≤ 1000` is a sum of two primes.
  - `legendre_upto_200`: Legendre's conjecture for `1 ≤ n ≤ 200`.
  - `oppermann_upto_200`: Oppermann's conjecture for `2 ≤ n ≤ 200`.
  These are checked by `decide` on a Boolean trial-division checker (`isPrimeB`) whose
  soundness (`isPrimeB_sound`) is proved, so the kernel does the arithmetic.

Missing from Mathlib (noted, not worked around): the Bombieri–Vinogradov theorem (the known
`θ < 1/2` case of Elliott–Halberstam) and the prime number theorem in arithmetic progressions
in the uniform form needed to state it; we therefore prove nothing about #83 beyond stating it.
-/

namespace CryptoLean.OpenProblems.NumberTheory.PrimeGaps

open Filter Asymptotics Finset

/-! ## Statements of the open problems -/

/-- **Binary Goldbach conjecture** (ProofAtlas #24, OPEN).

ProofAtlas exactTarget: "Prove or disprove that every even integer n greater than 2 is the sum
of two primes."

Modelling: `n : ℕ`; "prime" is Mathlib's `Nat.Prime`; the two primes may coincide.  We state
the "prove" direction as the `Prop`; "disprove" is its negation. -/
def BinaryGoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Chebyshev's function in an arithmetic progression:
`ψ(y; q, a) = ∑_{n ≤ y, n ≡ a (mod q)} Λ(n)`, for real `y` (sum over `1 ≤ n ≤ ⌊y⌋`). -/
noncomputable def psiAP (y : ℝ) (q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun n => n ≡ a [MOD q]), ArithmeticFunction.vonMangoldt n

/-- The maximal Chebyshev error `max_{y ≤ x} max_{(a,q)=1} |ψ(y;q,a) - y/φ(q)|`.
`y` ranges over the real interval `[0, x]` and `a` over the reduced residues `0 ≤ a < q` with
`gcd(a, q) = 1`.  (For `q ≥ 1` the inner set is bounded, so the supremum is a genuine maximum
of a finite family of bounded functions; on `ℝ` the empty supremum is `0`, matching the fact
that all terms are `≥ 0`.) -/
noncomputable def maxChebyshevError (x : ℝ) (q : ℕ) : ℝ :=
  ⨆ (y : ℝ) (_ : y ∈ Set.Icc (0 : ℝ) x) (a : ℕ) (_ : a < q ∧ Nat.Coprime a q),
    |psiAP y q a - y / (Nat.totient q : ℝ)|

/-- **Elliott–Halberstam conjecture** (ProofAtlas #83, OPEN).

ProofAtlas exactTarget: "Prove that for every A > 0 and every 0 < theta < 1, the sum over
q <= x^theta of the maximal Chebyshev error |psi(y; q, a) - y/phi(q)| over y <= x and (a,q)=1 is
O(x / (log x)^A), extending Bombieri-Vinogradov from theta < 1/2 to every theta < 1."

Modelling: `q` ranges over `1 ≤ q ≤ ⌊x^θ⌋`; `y` over real `0 ≤ y ≤ x`; `a` over residues
`0 ≤ a < q` coprime to `q`; `ψ` is `psiAP` (von Mangoldt sum); `O(·)` is Mathlib's `=O[atTop]`
as `x → ∞` over the reals; the implied constant may depend on `A` and `θ`. -/
def ElliottHalberstamConjecture : Prop :=
  ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ < 1 →
    (fun x : ℝ => ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, maxChebyshevError x q)
      =O[atTop] (fun x : ℝ => x / Real.log x ^ A)

/-- The `n`-th prime, `p_0 = 2, p_1 = 3, …` (Mathlib `Nat.nth Nat.Prime`). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- **Cramér's conjecture** (ProofAtlas #148, OPEN).

ProofAtlas exactTarget: "Prove that lim sup_{n -> infinity} (p_{n+1} - p_n) / (log p_n)^2 = 1,
where p_n is the n-th prime."

Modelling: `p_n = Nat.nth Nat.Prime n` (0-indexed; the shift does not affect a `limsup`);
the `limsup` is taken in the extended reals `EReal`, so the statement also excludes the value
`+∞` (a real-valued `limsup` in Lean would silently return a junk value for an unbounded
sequence). -/
def CramerConjecture : Prop :=
  Filter.limsup
      (fun n : ℕ => ((((nthPrime (n + 1) - nthPrime n : ℕ) : ℝ) /
        Real.log (nthPrime n) ^ 2 : ℝ) : EReal))
      atTop = 1

/-- **Legendre's conjecture** (ProofAtlas #275, OPEN).

ProofAtlas exactTarget: "Prove that for every positive integer n there exists a prime p with
n^2 < p < (n+1)^2."

Modelling: `n p : ℕ`, `Nat.Prime`; strict inequalities as in the source. -/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- **Oppermann's conjecture** (ProofAtlas #445, OPEN; ProofAtlas status
`open_disputed_claim`).

ProofAtlas exactTarget: "For every integer n>1, prove or disprove that each of the open
intervals (n(n-1),n^2) and (n^2,n(n+1)) contains a prime."

Modelling: `n p : ℕ`, `Nat.Prime`; open intervals as strict inequalities; the "prove"
direction is the `Prop`. -/
def OppermannConjecture : Prop :=
  ∀ n : ℕ, 1 < n →
    (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
    (∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < n * (n + 1))

/-! ## Known results -/

/-- **Known result** (Bertrand's postulate; Chebyshev 1852, proof of Erdős 1932): for every
`n ≥ 1` there is a prime `p` with `n < p ≤ 2n`.  Taken from Mathlib (`Nat.bertrand`). -/
theorem bertrand_postulate (n : ℕ) (hn : n ≠ 0) :
    ∃ p, p.Prime ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand n hn

/-- **Known result** (consequence of Bertrand's postulate, Chebyshev 1852): for every `n ≥ 2`
there is a prime `p` with `n < p < 2n`. -/
theorem exists_prime_strict_between_two_mul (n : ℕ) (hn : 2 ≤ n) :
    ∃ p, p.Prime ∧ n < p ∧ p < 2 * n := by
  obtain ⟨p, hp, h1, h2⟩ := Nat.bertrand n (by omega)
  refine ⟨p, hp, h1, lt_of_le_of_ne h2 ?_⟩
  rintro rfl
  have := (Nat.prime_mul_iff.mp hp)
  rcases this with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-! ## Implications (logical reductions, not progress) -/

/-- Oppermann's conjecture implies Legendre's conjecture (the case `n = 1` of Legendre is the
prime `2 ∈ (1, 4)`; for `n ≥ 2`, `(n², n(n+1)) ⊆ (n², (n+1)²)`). -/
theorem oppermann_implies_legendre : OppermannConjecture → LegendreConjecture := by
  intro h n hn
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · obtain ⟨p, hp, a, b⟩ := (h n h1).2
    exact ⟨p, hp, a, by nlinarith⟩
  · have : n = 1 := by omega
    subst this
    exact ⟨2, Nat.prime_two, by norm_num, by norm_num⟩

/-- Legendre's conjecture implies a square-root bound on prime gaps: every interval
`(x, x + 4⌊√x⌋ + 4)` contains a prime.  (Take `n = ⌊√x⌋ + 1` in Legendre.) -/
theorem legendre_implies_prime_gap_bound (h : LegendreConjecture) (x : ℕ) :
    ∃ p, p.Prime ∧ x < p ∧ p < x + 4 * Nat.sqrt x + 4 := by
  obtain ⟨p, hp, a, b⟩ := h (Nat.sqrt x + 1) (by omega)
  have h1 := Nat.lt_succ_sqrt' x
  have h2 := Nat.sqrt_le' x
  refine ⟨p, hp, ?_, ?_⟩
  · simp only [Nat.succ_eq_add_one] at h1; omega
  · have : (Nat.sqrt x + 1 + 1) ^ 2 = Nat.sqrt x ^ 2 + 4 * Nat.sqrt x + 4 := by ring
    omega

/-! ## A sound Boolean primality checker (for finite checks) -/

/-- Trial division: `trialOK n fuel d` checks that no `m` with `d ≤ m`, `m² ≤ n` (and fewer
than `fuel` steps) divides `n`. -/
def trialOK (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, d => if n < d * d then true else if n % d = 0 then false else trialOK n fuel (d + 1)

theorem trialOK_spec (n : ℕ) : ∀ fuel d, trialOK n fuel d = true →
    ∀ m, d ≤ m → m < d + fuel → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d _ m h1 h2; omega
  | succ k ih =>
    intro d h m hdm hm hmn
    simp only [trialOK] at h
    split_ifs at h with h1 h2
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rcases Nat.eq_or_lt_of_le hdm with rfl | hlt
      · intro hd; exact h2 (Nat.mod_eq_zero_of_dvd hd)
      · exact ih (d + 1) h m hlt (by omega) hmn

/-- Boolean primality test by trial division up to `√n`. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && trialOK n n 2

theorem isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : n.Prime := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, ht⟩ := h
  by_contra hp
  have hsq := Nat.minFac_sq_le_self (by omega) hp
  have hmp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hle : n.minFac ≤ n := Nat.minFac_le (by omega)
  exact trialOK_spec n n 2 ht n.minFac hmp.two_le (by omega) (by nlinarith)
    (Nat.minFac_dvd n)

/-! ## Finite checks -/

/-- Boolean check that `n` is a sum of two primes `p + (n - p)` with `2 ≤ p ≤ n - 2`. -/
def goldbachB (n : ℕ) : Bool :=
  (List.range' 2 (n - 3)).any (fun p => isPrimeB p && isPrimeB (n - p))

theorem goldbachB_sound {n : ℕ} (h : goldbachB n = true) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  simp only [goldbachB, List.any_eq_true, List.mem_range', one_mul, Bool.and_eq_true] at h
  obtain ⟨p, ⟨i, hi, rfl⟩, h1, h2⟩ := h
  exact ⟨2 + i, n - (2 + i), isPrimeB_sound h1, isPrimeB_sound h2, by omega⟩

/-- **Finite check** (not progress on the conjecture): every even `n` with `4 ≤ n ≤ 1000` is a
sum of two primes. -/
theorem goldbach_upto_1000 :
    ∀ n : ℕ, 2 < n → n ≤ 1000 → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have hB : (List.range' 2 499).all (fun k => goldbachB (2 * k)) = true := by decide +kernel
  intro n h1 h2 ⟨k, hk⟩
  simp only [List.all_eq_true, List.mem_range', one_mul] at hB
  have := hB k ⟨k - 2, by omega, by omega⟩
  rw [hk]
  simpa [two_mul] using goldbachB_sound this

/-- Boolean check that the open interval `(lo, hi)` contains a prime. -/
def primeInB (lo hi : ℕ) : Bool :=
  (List.range' (lo + 1) (hi - lo - 1)).any isPrimeB

theorem primeInB_sound {lo hi : ℕ} (h : primeInB lo hi = true) :
    ∃ p, p.Prime ∧ lo < p ∧ p < hi := by
  simp only [primeInB, List.any_eq_true, List.mem_range', one_mul] at h
  obtain ⟨p, ⟨i, hi', rfl⟩, h1⟩ := h
  exact ⟨lo + 1 + i, isPrimeB_sound h1, by omega, by omega⟩

/-- **Finite check** (not progress on the conjecture): Legendre's conjecture holds for
`1 ≤ n ≤ 200`. -/
theorem legendre_upto_200 :
    ∀ n : ℕ, 1 ≤ n → n ≤ 200 → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  have hB : (List.range' 1 200).all (fun n => primeInB (n ^ 2) ((n + 1) ^ 2)) = true := by
    decide +kernel
  intro n h1 h2
  simp only [List.all_eq_true, List.mem_range', one_mul] at hB
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 200 ∧ 1 + i = n := ⟨n - 1, by omega, by omega⟩
  exact primeInB_sound (hB (1 + i) ⟨i, hi, rfl⟩)

/-- **Finite check** (not progress on the conjecture): Oppermann's conjecture holds for
`2 ≤ n ≤ 200`. -/
theorem oppermann_upto_200 :
    ∀ n : ℕ, 1 < n → n ≤ 200 →
      (∃ p : ℕ, p.Prime ∧ n * (n - 1) < p ∧ p < n ^ 2) ∧
      (∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < n * (n + 1)) := by
  have hB : (List.range' 2 199).all (fun n =>
      primeInB (n * (n - 1)) (n ^ 2) && primeInB (n ^ 2) (n * (n + 1))) = true := by
    decide +kernel
  intro n h1 h2
  simp only [List.all_eq_true, List.mem_range', one_mul, Bool.and_eq_true] at hB
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 199 ∧ 2 + i = n := ⟨n - 2, by omega, by omega⟩
  obtain ⟨a, b⟩ := hB (2 + i) ⟨i, hi, rfl⟩
  exact ⟨primeInB_sound a, primeInB_sound b⟩

end CryptoLean.OpenProblems.NumberTheory.PrimeGaps

open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms bertrand_postulate
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms exists_prime_strict_between_two_mul
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms oppermann_implies_legendre
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms legendre_implies_prime_gap_bound
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms goldbach_upto_1000
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms legendre_upto_200
open CryptoLean.OpenProblems.NumberTheory.PrimeGaps in
#print axioms oppermann_upto_200
