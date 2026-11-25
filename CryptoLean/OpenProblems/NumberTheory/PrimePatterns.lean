import Mathlib

/-!
# Prime patterns: twin primes, Polignac, Dickson, Schinzel, Bateman–Horn and relatives

ProofAtlas problems (by `releaseRank`):
* #18  Hardy–Littlewood prime `k`-tuple conjecture  → `HardyLittlewoodKTupleConjecture`
* #20  Twin prime conjecture                           → `TwinPrimeConjecture`
* #49  Dickson's conjecture                            → `DicksonConjecture`
* #52  Schinzel's Hypothesis H                         → `SchinzelHypothesisH`
* #78  Bateman–Horn conjecture                         → `BatemanHornConjecture`
* #93  Bunyakovsky conjecture                          → `BunyakovskyConjecture`
* #97  Polignac's conjecture                           → `PolignacConjecture`
* #179 Landau's fourth problem (`n² + 1`)              → `LandauFourthProblem`
* #433 Second Hardy–Littlewood conjecture              → `SecondHardyLittlewoodConjecture`
* #473 Infinitude of Sophie Germain primes             → `SophieGermainConjecture`

**All ten problems are open.**  Each appears below only as an unproved `def … : Prop`
whose docstring quotes the ProofAtlas `exactTarget` and lists the modelling choices.
Nothing in this file proves, or is evidence towards, any of them.

What *is* proved here:
* **Known results.**
  - `dickson_one_form`: the case `k = 1` of Dickson's conjecture, which is Dirichlet's
    theorem on primes in arithmetic progressions (taken from Mathlib,
    `Nat.forall_exists_prime_gt_and_zmodEq`).
  - `finite_of_fixed_prime_divisor`: necessity of the "no fixed prime divisor" hypothesis in
    Schinzel / Bunyakovsky / Dickson: if one prime divides `∏ fᵢ(n)` for every `n` and every
    `fᵢ` is non-constant, only finitely many `n` make all `fᵢ(n)` prime.
  - `primeCounting_add_two_le`: the subcase `y = 2` of the second Hardy–Littlewood
    conjecture, `π(x + 2) ≤ π(x) + π(2)` for `x ≥ 2` (elementary).
* **Implications between the conjectures** (logical reductions, not progress):
  `polignac_implies_twinPrime`, `dickson_implies_twinPrime`, `dickson_implies_sophieGermain`,
  `schinzel_implies_bunyakovsky`, `bunyakovsky_implies_landau`; and the identification
  `consecutivePrimeGapSet_two` of Polignac's gap-2 set with the twin-prime set.
* **Finite checks** (explicit witnesses or bounded ranges; these say nothing about the
  infinite statements): `twinPrime_witness_gt_1000`, `polignac_witnesses`,
  `landau_witnesses`, `sophieGermain_witnesses`, `secondHardyLittlewood_upto_30`.

Modelling conventions used throughout:
* "`z` is prime" for an integer `z` is `IsPosPrime z`: `z` is the cast of a natural prime
  (so negative associates of primes do *not* count).
* Polynomials are `ℤ[X]` (`Polynomial ℤ`); "irreducible" is Mathlib's `Irreducible` in `ℤ[X]`
  (for a polynomial with positive leading coefficient this is the usual notion: primitive
  and irreducible over `ℚ`, or a constant prime — the latter is excluded by the fixed-divisor
  hypothesis in every statement).
* Asymptotic equivalence `f ~ g` is Mathlib's `Asymptotics.IsEquivalent Filter.atTop`.
* Singular series / Bateman–Horn constants are formalised as the limit of the partial Euler
  products over primes `p ≤ y`, `y → ∞`; the conjectures assert that this limit exists *and*
  the asymptotic holds with it.  (Convergence of these products is itself known; including it
  in the statement only makes the conjectured constant well defined.)
-/

namespace CryptoLean.OpenProblems.NumberTheory.PrimePatterns

open Polynomial Finset Filter Asymptotics

/-! ## Basic notions -/

/-- An integer `z` is a (positive) prime: it is the cast of a natural prime number. -/
def IsPosPrime (z : ℤ) : Prop := ∃ p : ℕ, p.Prime ∧ (p : ℤ) = z

lemma isPosPrime_natCast (n : ℕ) : IsPosPrime (n : ℤ) ↔ n.Prime := by
  constructor
  · rintro ⟨p, hp, h⟩
    have : p = n := by exact_mod_cast h
    exact this ▸ hp
  · intro h; exact ⟨n, h, rfl⟩

/-! ## #20 Twin primes -/

/-- **Twin Prime Conjecture** (ProofAtlas #20, OPEN).

ProofAtlas exactTarget: "Prove that there are infinitely many primes p such that p+2 is also
prime."

Modelling: the set `{p : ℕ | p prime ∧ p + 2 prime}` is infinite (`Set.Infinite`).
No simplification. -/
def TwinPrimeConjecture : Prop :=
  {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite

/-! ## #473 Sophie Germain primes -/

/-- **Infinitude of Sophie Germain primes** (ProofAtlas #473, OPEN).

ProofAtlas exactTarget: "Determine whether there are infinitely many Sophie Germain primes,
that is, primes p such that 2p + 1 is also prime."

Modelling: "determine whether" is formalised as the expected (affirmative) answer: the set
`{p : ℕ | p prime ∧ 2p + 1 prime}` is infinite.  A proof of the negation would settle the
problem the other way. -/
def SophieGermainConjecture : Prop :=
  {p : ℕ | p.Prime ∧ (2 * p + 1).Prime}.Infinite

/-! ## #179 Landau's fourth problem -/

/-- **Landau's fourth problem** (ProofAtlas #179, OPEN).

ProofAtlas exactTarget: "Prove or disprove that there are infinitely many primes of the form
n^2+1 with n a positive integer."

Modelling: the set of primes `p` such that `p = n² + 1` for some natural `n > 0` is infinite.
"Prove or disprove" is formalised as the affirmative statement (its negation is the
disproof). -/
def LandauFourthProblem : Prop :=
  {p : ℕ | p.Prime ∧ ∃ n : ℕ, 0 < n ∧ p = n ^ 2 + 1}.Infinite

/-! ## #97 Polignac -/

/-- Primes `p` such that `p` and `p + g` are **consecutive** primes (no prime strictly in
between). -/
def consecutivePrimeGapSet (g : ℕ) : Set ℕ :=
  {p | p.Prime ∧ (p + g).Prime ∧ ∀ q, p < q → q < p + g → ¬ q.Prime}

/-- **Polignac's conjecture** (ProofAtlas #97, OPEN).

ProofAtlas exactTarget: "For every positive even integer 2k, there are infinitely many pairs of
consecutive primes whose difference is 2k."

Modelling: for every natural `k ≥ 1`, infinitely many primes `p` such that `p + 2k` is the
next prime after `p`.  A pair of consecutive primes is determined by its smaller member, so
counting pairs is the same as counting `p`.  No simplification. -/
def PolignacConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → (consecutivePrimeGapSet (2 * k)).Infinite

/-! ## #433 Second Hardy–Littlewood conjecture -/

/-- **Second Hardy–Littlewood conjecture** (ProofAtlas #433, OPEN).

ProofAtlas exactTarget: "Prove or disprove that pi(x+y) <= pi(x)+pi(y) for all integers
x,y >= 2, where pi is the prime-counting function."

Modelling: `π` is Mathlib's `Nat.primeCounting` (`π n = #{p ≤ n | p prime}`); `x, y` range
over naturals `≥ 2`.  "Prove or disprove" is formalised as the affirmative statement.
(It is widely expected to be false, since it is incompatible with the prime `k`-tuple
conjecture by Hensley–Richards 1974; but it is open.) -/
def SecondHardyLittlewoodConjecture : Prop :=
  ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y

/-! ## #49 Dickson -/

/-- **Dickson's conjecture** (ProofAtlas #49, OPEN; solved subcase `k = 1` is Dirichlet).

ProofAtlas exactTarget: "For every integer k>=1 and every family f_i(n)=a_i*n+b_i (1<=i<=k)
with integers a_i>=1 and b_i, if for each prime p some integer n has p not dividing the
product of the f_i(n), then infinitely many positive integers n make every f_i(n) prime."

Modelling: the family is indexed by `Fin k`; "f_i(n) prime" is `IsPosPrime` (a positive
rational prime); "infinitely many positive integers n" is `Set.Infinite` of a set of naturals
`n > 0`.  No simplification. -/
def DicksonConjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ a b : Fin k → ℤ, (∀ i, 1 ≤ a i) →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ i, (a i * n + b i)) →
    {n : ℕ | 0 < n ∧ ∀ i, IsPosPrime (a i * n + b i)}.Infinite

/-! ## #52 Schinzel's Hypothesis H and #93 Bunyakovsky -/

/-- **Schinzel's Hypothesis H** (ProofAtlas #52, OPEN).

ProofAtlas exactTarget: "Let f1,...,fr in Z[x] be irreducible with positive leading
coefficients and no prime dividing f1(n)...fr(n) for every n. Prove that infinitely many
positive integers n make every fi(n) prime."

Modelling: `f : Fin r → ℤ[X]`; irreducible is `Irreducible` in `ℤ[X]`; "no prime dividing
f1(n)...fr(n) for every n" is: for each prime `p` there is an integer `n` with
`p ∤ ∏ fᵢ(n)`; "fi(n) prime" is `IsPosPrime`.  No simplification. -/
def SchinzelHypothesisH : Prop :=
  ∀ (r : ℕ) (f : Fin r → ℤ[X]), (∀ i, Irreducible (f i)) → (∀ i, 0 < (f i).leadingCoeff) →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ i, (f i).eval n) →
    {n : ℕ | 0 < n ∧ ∀ i, IsPosPrime ((f i).eval (n : ℤ))}.Infinite

/-- **Bunyakovsky conjecture** (ProofAtlas #93, OPEN; ProofAtlas notes a disputed claim,
which is not accepted here).

ProofAtlas exactTarget: "Prove or disprove that every irreducible polynomial f in Z[x] with
positive leading coefficient and no fixed prime divisor takes prime values for infinitely
many positive integer inputs."

Modelling: irreducible is `Irreducible` in `ℤ[X]`; "no fixed prime divisor" is: for each
prime `p` some integer `n` has `p ∤ f(n)`; "takes prime values for infinitely many positive
integer inputs" is: `{n : ℕ | n > 0 ∧ f(n) is a positive prime}` is infinite.  "Prove or
disprove" is formalised as the affirmative statement. -/
def BunyakovskyConjecture : Prop :=
  ∀ f : ℤ[X], Irreducible f → 0 < f.leadingCoeff →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ f.eval n) →
    {n : ℕ | 0 < n ∧ IsPosPrime (f.eval (n : ℤ))}.Infinite

/-! ## #78 Bateman–Horn -/

/-- `ω(p)`: the number of residues `m mod p` (`0 ≤ m < p`) with `p ∣ ∏ fᵢ(m)`. -/
def bhOmega {r : ℕ} (f : Fin r → ℤ[X]) (p : ℕ) : ℕ :=
  ((range p).filter (fun m : ℕ => (p : ℤ) ∣ ∏ i, (f i).eval (m : ℤ))).card

/-- Partial Bateman–Horn Euler product `∏_{p ≤ y} (1 - ω(p)/p) / (1 - 1/p)^r`. -/
noncomputable def bhPartialProduct {r : ℕ} (f : Fin r → ℤ[X]) (y : ℕ) : ℝ :=
  ∏ p ∈ (range (y + 1)).filter Nat.Prime,
    (1 - (bhOmega f p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ r

open Classical in
/-- `#{1 ≤ n ≤ N : every fᵢ(n) is a positive prime}`. -/
noncomputable def simulPrimeCount {r : ℕ} (f : Fin r → ℤ[X]) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n : ℕ => ∀ i, IsPosPrime ((f i).eval (n : ℤ)))).card

/-- **Bateman–Horn conjecture** (ProofAtlas #78, OPEN; solved subcases e.g. one linear
polynomial = prime number theorem in progressions).

ProofAtlas exactTarget: "Prove or disprove the Bateman-Horn asymptotic formula for the number
of positive integers n up to x for which any fixed admissible finite family of distinct
irreducible integer polynomials with positive leading coefficients are simultaneously prime."

Modelling (the standard Bateman–Horn formula):
* the family is `f : Fin r → ℤ[X]`, injective (distinct), each `Irreducible` in `ℤ[X]` with
  positive leading coefficient; admissible means: for every prime `p` some integer `n` has
  `p ∤ ∏ fᵢ(n)` (equivalently `ω(p) < p`);
* `Q(x) = #{1 ≤ n ≤ ⌊x⌋ : all fᵢ(n) positive primes}` (`simulPrimeCount f ⌊x⌋₊`);
* the constant is `C = ∏_p (1 - ω(p)/p)(1 - 1/p)^{-r}`, formalised as the limit `C` of the
  partial products over `p ≤ y` (`bhPartialProduct`); the statement asserts that this limit
  exists and that
  `Q(x) ~ C / (∏ deg fᵢ) · ∫_2^x dt / (log t)^r`  as `x → ∞`.
* "Prove or disprove" is formalised as the affirmative statement. -/
def BatemanHornConjecture : Prop :=
  ∀ (r : ℕ) (f : Fin r → ℤ[X]), Function.Injective f → (∀ i, Irreducible (f i)) →
    (∀ i, 0 < (f i).leadingCoeff) →
    (∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ i, (f i).eval n) →
    ∃ C : ℝ, Tendsto (bhPartialProduct f) atTop (nhds C) ∧
      (fun x : ℝ => (simulPrimeCount f ⌊x⌋₊ : ℝ)) ~[atTop]
        (fun x : ℝ => C / (∏ i, ((f i).natDegree : ℝ)) *
          ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ r)

/-! ## #18 Hardy–Littlewood prime k-tuples -/

/-- A finite set `H ⊆ ℤ` is **admissible** if for every prime `p` it misses some residue class
mod `p`. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ m : ℤ, ∀ h ∈ H, ¬ (p : ℤ) ∣ h - m

/-- `ν_H(p)`: the number of residues `m mod p` (`0 ≤ m < p`) such that `p ∣ m + h` for some
`h ∈ H`, i.e. the number of residue classes mod `p` occupied by `-H` (equivalently by `H`). -/
def hlNu (H : Finset ℤ) (p : ℕ) : ℕ :=
  ((range p).filter (fun m : ℕ => ∃ h ∈ H, (p : ℤ) ∣ (m : ℤ) + h)).card

/-- Partial singular series `∏_{p ≤ y} (1 - ν_H(p)/p) / (1 - 1/p)^k`, `k = |H|`. -/
noncomputable def hlPartialProduct (H : Finset ℤ) (y : ℕ) : ℝ :=
  ∏ p ∈ (range (y + 1)).filter Nat.Prime,
    (1 - (hlNu H p : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ H.card

open Classical in
/-- `#{1 ≤ n ≤ N : n + h is a positive prime for every h ∈ H}`. -/
noncomputable def kTupleCount (H : Finset ℤ) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n : ℕ => ∀ h ∈ H, IsPosPrime ((n : ℤ) + h))).card

/-- **Hardy–Littlewood prime `k`-tuple conjecture** (ProofAtlas #18, OPEN).

ProofAtlas exactTarget: "For every finite admissible set H={h_1,...,h_k} of distinct integers,
prove that the number of n <= x for which every n+h_i is prime is asymptotic to
S(H)x/(log x)^k, where S(H) is the Hardy-Littlewood singular series, or disprove this
formula."

Modelling:
* `H : Finset ℤ` (distinct integers), `k = H.card`, admissibility as in `Admissible`;
* the count is over `1 ≤ n ≤ ⌊x⌋` (`kTupleCount H ⌊x⌋₊`).  Restricting to `n ≥ 1` changes
  the count by at most a bounded amount (`n + hᵢ ≥ 2` forces `n ≥ 2 - min H`), so the
  asymptotic is unaffected;
* `S(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-k}` is formalised as the limit of the partial
  products over `p ≤ y`; the statement asserts the limit exists and the asymptotic holds;
* "or disprove" is formalised as the affirmative statement. -/
def HardyLittlewoodKTupleConjecture : Prop :=
  ∀ H : Finset ℤ, Admissible H →
    ∃ S : ℝ, Tendsto (hlPartialProduct H) atTop (nhds S) ∧
      (fun x : ℝ => (kTupleCount H ⌊x⌋₊ : ℝ)) ~[atTop]
        (fun x : ℝ => S * x / Real.log x ^ H.card)

/-! ## Known results -/

/-- **Known result** (Dirichlet 1837; in Mathlib as
`Nat.forall_exists_prime_gt_and_zmodEq`): the case `k = 1` of Dickson's conjecture.  If
`a ≥ 1` and for every prime `p` some `n` has `p ∤ a n + b` (equivalently `gcd(a, b) = 1`),
then `a n + b` is prime for infinitely many positive integers `n`. -/
theorem dickson_one_form (a b : ℤ) (ha : 1 ≤ a)
    (hadm : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ a * n + b) :
    {n : ℕ | 0 < n ∧ IsPosPrime (a * n + b)}.Infinite := by
  -- admissibility forces `gcd(b, a) = 1`
  have hcop : IsCoprime b a := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpb : (p : ℤ) ∣ b := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_left b a)
    have hpa : (p : ℤ) ∣ a := (Int.natCast_dvd_natCast.mpr hpg).trans (Int.gcd_dvd_right b a)
    obtain ⟨n, hn⟩ := hadm p hp
    exact hn (dvd_add (dvd_mul_of_dvd_left hpa n) hpb)
  set q : ℕ := a.toNat with hqdef
  have hq : (q : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hq0 : q ≠ 0 := by omega
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨p, hpN, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq ((N + 1) * q + b.natAbs)
    hq0 (a := b) (by rw [hq]; exact hcop)
  have hdvd : a ∣ (p : ℤ) - b := by rw [← hq]; exact hpmod.symm.dvd
  obtain ⟨m, hm⟩ := hdvd
  have hpN' : ((N + 1) * q + b.natAbs : ℤ) < p := by exact_mod_cast hpN
  rw [hq] at hpN'
  have hbabs : b ≤ (b.natAbs : ℤ) := Int.le_natAbs
  have hm' : (N : ℤ) + 1 < m := by
    by_contra hcon
    push Not at hcon
    have : a * m ≤ a * ((N : ℤ) + 1) := mul_le_mul_of_nonneg_left hcon (by omega)
    nlinarith
  refine ⟨m.toNat, ⟨by omega, p, hp, ?_⟩, by omega⟩
  rw [Int.toNat_of_nonneg (by omega)]
  linarith

/-- **Known result**: Dickson's conjecture holds for every family with `k = 1` (Dirichlet's
theorem; see `dickson_one_form`). -/
theorem dicksonConjecture_k_one (a b : Fin 1 → ℤ) (ha : ∀ i, 1 ≤ a i)
    (hadm : ∀ p : ℕ, p.Prime → ∃ n : ℤ, ¬ (p : ℤ) ∣ ∏ i, (a i * n + b i)) :
    {n : ℕ | 0 < n ∧ ∀ i, IsPosPrime (a i * n + b i)}.Infinite := by
  have h := dickson_one_form (a 0) (b 0) (ha 0) (by simpa using hadm)
  refine h.mono ?_
  rintro n ⟨hn0, hn⟩
  refine ⟨hn0, fun i => ?_⟩
  rwa [Subsingleton.elim i 0]

/-- **Known result** (folklore; the reason for the hypothesis in Bunyakovsky 1857 /
Schinzel–Sierpiński 1958): the "no fixed prime divisor" condition is necessary.  If a prime
`p` divides `∏ fᵢ(n)` for every integer `n` and every `fᵢ` is non-constant, then only finitely
many natural `n` make all `fᵢ(n)` prime (for each such `n`, some `fᵢ(n) = p`). -/
theorem finite_of_fixed_prime_divisor {r : ℕ} (f : Fin r → ℤ[X])
    (hdeg : ∀ i, 0 < (f i).natDegree) (p : ℕ) (hp : p.Prime)
    (hfix : ∀ n : ℤ, (p : ℤ) ∣ ∏ i, (f i).eval n) :
    {n : ℕ | ∀ i, IsPosPrime ((f i).eval (n : ℤ))}.Finite := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsub : {n : ℕ | ∀ i, IsPosPrime ((f i).eval (n : ℤ))} ⊆
      ⋃ i, (Nat.cast : ℕ → ℤ) ⁻¹' ((f i - C (p : ℤ)).roots.toFinset : Set ℤ) := by
    intro n hn
    obtain ⟨i, -, hi⟩ := (hpZ.dvd_finsetProd_iff _).mp (hfix n)
    obtain ⟨q, hq, hqe⟩ := hn i
    rw [← hqe] at hi
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (by exact_mod_cast hi)
    have hne : f i - C (p : ℤ) ≠ 0 := by
      intro h0
      have : f i = C (p : ℤ) := sub_eq_zero.mp h0
      have h1 := hdeg i
      rw [this, natDegree_C] at h1
      exact lt_irrefl 0 h1
    simp only [Set.mem_iUnion, Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    refine ⟨i, (mem_roots hne).mpr ?_⟩
    simp [IsRoot, ← hqe, hpq]
  refine Set.Finite.subset (Set.finite_iUnion fun i => ?_) hsub
  exact Set.Finite.preimage Nat.cast_injective.injOn (Finset.finite_toSet _)

/-- **Known result** (elementary; the subcase `y = 2` of the second Hardy–Littlewood
conjecture, cf. Hardy–Littlewood, *Acta Math.* 44 (1923)): for every `x ≥ 2`,
`π(x + 2) ≤ π(x) + π(2)`, because one of `x + 1, x + 2` is even and `≥ 4`. -/
theorem primeCounting_add_two_le (x : ℕ) (hx : 2 ≤ x) :
    Nat.primeCounting (x + 2) ≤ Nat.primeCounting x + Nat.primeCounting 2 := by
  have h2 : Nat.primeCounting 2 = 1 := by decide
  rw [h2]
  simp only [Nat.primeCounting, Nat.primeCounting', show x + 2 + 1 = (x + 1) + 1 + 1 by ring,
    Nat.count_succ]
  rcases Nat.even_or_odd x with he | ho
  · -- `x + 2` is even and `≥ 4`
    have : ¬ (x + 1 + 1).Prime := by
      intro hp
      have : x + 1 + 1 = 2 := hp.even_iff.mp (by rw [add_assoc]; exact he.add (by decide))
      omega
    simp only [this, ite_false]
    split_ifs <;> omega
  · have : ¬ (x + 1).Prime := by
      intro hp
      have : x + 1 = 2 := hp.even_iff.mp ho.add_one
      omega
    simp only [this, ite_false]
    split_ifs <;> omega

/-! ## Implications between the conjectures (logical reductions only) -/

/-- Polignac's gap-`2` set is exactly the twin-prime set (for twin primes `p, p+2`,
`p + 1` is never prime). -/
theorem consecutivePrimeGapSet_two :
    consecutivePrimeGapSet 2 = {p : ℕ | p.Prime ∧ (p + 2).Prime} := by
  ext p
  simp only [consecutivePrimeGapSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    intro q hq1 hq2 hq
    have hq' : q = p + 1 := by omega
    subst hq'
    rcases h1.eq_two_or_odd' with rfl | hodd
    · norm_num at h2
    · have he : Even (p + 1) := hodd.add_one
      have : p + 1 = 2 := hq.even_iff.mp he
      have : p = 1 := by omega
      subst this; exact Nat.not_prime_one h1

/-- Polignac's conjecture (case `k = 1`) implies the twin prime conjecture. -/
theorem polignac_implies_twinPrime : PolignacConjecture → TwinPrimeConjecture := by
  intro h
  have := h 1 le_rfl
  rw [show 2 * 1 = 2 from rfl, consecutivePrimeGapSet_two] at this
  exact this

/-- Dickson's conjecture (forms `n, n + 2`) implies the twin prime conjecture. -/
theorem dickson_implies_twinPrime : DicksonConjecture → TwinPrimeConjecture := by
  intro h
  have hinf := h 2 (by norm_num) ![1, 1] ![0, 2] (by intro i; fin_cases i <;> simp) (by
    intro p hp
    by_cases h3 : p = 3
    · subst h3; exact ⟨2, by simp [Fin.prod_univ_two]⟩
    · refine ⟨1, ?_⟩
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      intro hd
      have : p ∣ 3 := by exact_mod_cast hd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this))
  refine hinf.mono ?_
  rintro n ⟨-, hn⟩
  have h0 := hn 0
  have h1 := hn 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, add_zero] at h0 h1
  have h1' : IsPosPrime ((n + 2 : ℕ) : ℤ) := by push_cast; exact h1
  exact ⟨(isPosPrime_natCast n).mp h0, (isPosPrime_natCast _).mp h1'⟩

/-- Dickson's conjecture (forms `n, 2n + 1`) implies infinitude of Sophie Germain primes. -/
theorem dickson_implies_sophieGermain : DicksonConjecture → SophieGermainConjecture := by
  intro h
  have hinf := h 2 (by norm_num) ![1, 2] ![0, 1] (by intro i; fin_cases i <;> simp) (by
    intro p hp
    by_cases h3 : p = 3
    · subst h3; exact ⟨2, by simp [Fin.prod_univ_two]⟩
    · refine ⟨1, ?_⟩
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
      intro hd
      have : p ∣ 3 := by exact_mod_cast hd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this))
  refine hinf.mono ?_
  rintro n ⟨-, hn⟩
  have h0 := hn 0
  have h1 := hn 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, add_zero] at h0 h1
  have h1' : IsPosPrime ((2 * n + 1 : ℕ) : ℤ) := by push_cast; exact h1
  exact ⟨(isPosPrime_natCast n).mp h0, (isPosPrime_natCast _).mp h1'⟩

/-- Schinzel's Hypothesis H (case `r = 1`) implies the Bunyakovsky conjecture. -/
theorem schinzel_implies_bunyakovsky : SchinzelHypothesisH → BunyakovskyConjecture := by
  intro h f hirr hlc hfix
  have hinf := h 1 ![f] (by intro i; fin_cases i; simpa using hirr)
    (by intro i; fin_cases i; simpa using hlc) (by simpa using hfix)
  refine hinf.mono ?_
  rintro n ⟨hn0, hn⟩
  exact ⟨hn0, by simpa using hn 0⟩

/-- `X² + 1` is irreducible in `ℤ[X]` (it is the 4th cyclotomic polynomial). -/
lemma irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  have h := Polynomial.cyclotomic.irreducible (n := 4) (by norm_num)
  have : cyclotomic 4 ℤ = X ^ 2 + 1 := by
    have := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two
    norm_num at this
    rw [this]
  rwa [this] at h

/-- The Bunyakovsky conjecture (for `X² + 1`) implies Landau's fourth problem. -/
theorem bunyakovsky_implies_landau : BunyakovskyConjecture → LandauFourthProblem := by
  intro h
  have hlc : (0 : ℤ) < (X ^ 2 + 1 : ℤ[X]).leadingCoeff := by
    have hm : (X ^ 2 + 1 : ℤ[X]).Monic := by
      simpa using monic_X_pow_add_C (1 : ℤ) two_ne_zero
    rw [hm.leadingCoeff]; norm_num
  have hinf := h (X ^ 2 + 1) irreducible_X_sq_add_one hlc (by
    intro p hp
    by_cases h2 : p = 2
    · subst h2; exact ⟨2, by norm_num⟩
    · refine ⟨1, ?_⟩
      norm_num
      intro hd
      have : p ∣ 2 := by exact_mod_cast hd
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this))
  have himg := hinf.image (f := fun n : ℕ => n ^ 2 + 1) (by
    intro a _ b _ hab
    simp only at hab
    have : a ^ 2 = b ^ 2 := by omega
    exact Nat.pow_left_injective (by norm_num) this)
  refine himg.mono ?_
  rintro _ ⟨n, ⟨hn0, hn⟩, rfl⟩
  have hn' : IsPosPrime ((n ^ 2 + 1 : ℕ) : ℤ) := by push_cast; simpa using hn
  exact ⟨(isPosPrime_natCast _).mp hn', n, hn0, rfl⟩

/-! ## Finite checks (no bearing on the infinite statements) -/

/-- **Finite check**: there is a twin-prime pair above 1000 (`1019, 1021`). -/
theorem twinPrime_witness_gt_1000 : ∃ p, 1000 < p ∧ p.Prime ∧ (p + 2).Prime :=
  ⟨1019, by norm_num, by norm_num, by norm_num⟩

/-- **Finite check**: for each gap `2k`, `1 ≤ k ≤ 5`, there is at least one pair of
consecutive primes with that gap (`3,5`; `7,11`; `23,29`; `89,97`; `139,149`). -/
theorem polignac_witnesses : ∀ k, 1 ≤ k → k ≤ 5 → (consecutivePrimeGapSet (2 * k)).Nonempty := by
  intro k hk1 hk5
  interval_cases k
  · refine ⟨3, by norm_num, by norm_num, ?_⟩
    intro q h1 h2; interval_cases q; norm_num
  · refine ⟨7, by norm_num, by norm_num, ?_⟩
    intro q h1 h2; interval_cases q <;> norm_num
  · refine ⟨23, by norm_num, by norm_num, ?_⟩
    intro q h1 h2; interval_cases q <;> norm_num
  · refine ⟨89, by norm_num, by norm_num, ?_⟩
    intro q h1 h2; interval_cases q <;> norm_num
  · refine ⟨139, by norm_num, by norm_num, ?_⟩
    intro q h1 h2; interval_cases q <;> norm_num

/-- **Finite check**: `n² + 1` is prime for `n = 1, 2, 4, 6, 10, 14, 16, 20, 24, 26`. -/
theorem landau_witnesses :
    ∀ n ∈ ({1, 2, 4, 6, 10, 14, 16, 20, 24, 26} : Finset ℕ), (n ^ 2 + 1).Prime := by
  intro n hn; fin_cases hn <;> norm_num

/-- **Finite check**: `p` and `2p + 1` are both prime for
`p = 2, 3, 5, 11, 23, 29, 41, 53, 83, 89`. -/
theorem sophieGermain_witnesses :
    ∀ p ∈ ({2, 3, 5, 11, 23, 29, 41, 53, 83, 89} : Finset ℕ), p.Prime ∧ (2 * p + 1).Prime := by
  intro p hp; fin_cases hp <;> norm_num

/-- **Finite check**: `π(x + y) ≤ π(x) + π(y)` for all `2 ≤ x, y ≤ 30`. -/
theorem secondHardyLittlewood_upto_30 :
    ∀ x ≤ 30, ∀ y ≤ 30, 2 ≤ x → 2 ≤ y →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y := by
  decide

end CryptoLean.OpenProblems.NumberTheory.PrimePatterns

#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.dickson_one_form
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.dicksonConjecture_k_one
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.finite_of_fixed_prime_divisor
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.primeCounting_add_two_le
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.consecutivePrimeGapSet_two
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.polignac_implies_twinPrime
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.dickson_implies_twinPrime
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.dickson_implies_sophieGermain
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.schinzel_implies_bunyakovsky
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.irreducible_X_sq_add_one
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.bunyakovsky_implies_landau
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.twinPrime_witness_gt_1000
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.polignac_witnesses
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.landau_witnesses
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.sophieGermain_witnesses
#print axioms CryptoLean.OpenProblems.NumberTheory.PrimePatterns.secondHardyLittlewood_upto_30
