import Mathlib

/-!
# Lattice-point and divisor problems, and Waring's function `G(k)`

ProofAtlas problems (releaseRank) 153, 181, 230, 374.

**All four problems are OPEN.** Each appears below only as an unproved `def … : Prop` whose
docstring quotes the ProofAtlas `exactTarget` and lists the modelling choices.  Nothing in this
file proves, or claims progress towards, any of them.  (Problem 153 is recorded by ProofAtlas as
`open_disputed_claim`: claimed resolutions exist in the literature but none is accepted.)

Mathlib objects reused (no re-definitions):
* `Nat.divisors` (so `d(n) = n.divisors.card`), `Real.eulerMascheroniConstant`, `Real.log`,
  `Asymptotics.IsBigO` (`=O[atTop]`), `Real.rpow`;
* `riemannZeta` and `circleIntegral` (to write `Res_{s=1}` as a contour integral);
* `Nat.sum_four_squares` (Lagrange), `harmonic`, `log_le_harmonic_floor`,
  `harmonic_floor_le_one_add_log`, `Real.eulerMascheroniConstant_lt_two_thirds`.

## What is missing from Mathlib (gap notes)

* **Hilbert's theorem (Waring's problem)** that some `s` works for every `k` is not in Mathlib,
  so `waringG k` is a `sInf` that would be the junk value `0` if no `s` worked.  The open
  statement `waringG 3 = 4` is not affected (it forces the set to be non-empty), and the lower
  bounds proved below are stated for every admissible `s`, not for `waringG`.
* **Laurent expansion / residues of `ζ` at `s = 1`.**  Mathlib has no residue operator; the
  main term of the Piltz problem is written as `(2πi)⁻¹ ∮_{|s-1|=1/2} ζ(s)^k x^s / s ds`, which
  equals `Res_{s=1}` by the residue theorem because `ζ` is holomorphic on `ℂ ∖ {1}` and `1/s` is
  holomorphic on the closed disc `|s - 1| ≤ 1/2`.
* **Elementary error bounds** `Δ(x) = O(√x)` (Dirichlet's hyperbola method) and
  `E(r) = O(r)` (Gauss's unit-square argument) are classical but were **not** formalised here
  (dropped after the plan stage; see the summary).  Only the weaker `Δ(x) = O(x)` is proved.

## Known results proved here

* `sum_card_divisors_eq_sum_div`: `∑_{n ≤ N} d(n) = ∑_{d ≤ N} ⌊N/d⌋` (exact identity).
* `abs_divisorDelta_le`, `divisorDelta_isBigO_self`, `one_mem_divisorExponentSet`:
  the trivial bound `|Δ(x)| ≤ 2x` for `x ≥ 1`, hence the exponent `a = 1` is admissible.
* `waringG_two`: `G(2) = 4` (Lagrange four squares, and `8m + 7` is never a sum of 3 squares).
* `not_isWaringBound_two_three`: infinitely many integers need four squares.
* `four_le_of_isWaringBound_three`: `G(3) ≥ 4` (cubes mod 9).
* `fifteen_le_of_isWaringBound_four`: `G(4) ≥ 15` (fourth powers mod 16; the true value
  `G(4) = 16`, Davenport 1939, is not formalised).
* `piltzD_two`: the `k = 2` case of the Piltz count is the divisor function.
-/

namespace CryptoLean.OpenProblems.NumberTheory.LatticeDivisor

open Filter Asymptotics Finset
open scoped Real

/-! ## Problem 153: the Dirichlet divisor problem -/

/-- `Δ(x) = ∑_{1 ≤ n ≤ x} d(n) - x log x - (2γ - 1) x`, with `d(n) = n.divisors.card`. -/
noncomputable def divisorDelta (x : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊x⌋₊, ((n.divisors.card : ℕ) : ℝ)) - x * Real.log x
    - (2 * Real.eulerMascheroniConstant - 1) * x

/-- The admissible exponents `{a : ∀ ε > 0, Δ(x) = O_ε(x^{a+ε})}`. -/
def divisorExponentSet : Set ℝ :=
  {a | ∀ ε > 0, divisorDelta =O[atTop] fun x : ℝ => x ^ (a + ε)}

/-- `α₂ = inf {a : ∀ ε > 0, Δ(x) = O_ε(x^{a+ε})}` (a real `sInf`; junk `0` if the set were
empty or unbounded below — neither is the case mathematically). -/
noncomputable def divisorExponent : ℝ := sInf divisorExponentSet

/-- **Problem 153 (OPEN; ProofAtlas status `open_disputed_claim`).**  ProofAtlas `exactTarget`:

> "Let d(n) count the positive divisors of n and Delta(x)=sum_{n<=x} d(n)-x log x-(2 gamma-1)x
> for real x>=2. Determine the optimal exponent alpha_2=inf{a: for every epsilon>0,
> Delta(x)=O_epsilon(x^(a+epsilon)) as x tends to infinity}."

Modelling choices:
* "Determine `α₂`" is not a proposition; it is rendered as the standard conjecture `α₂ = 1/4`
  (Hardy–Landau: `α₂ ≥ 1/4` is known, so this says the conjectured value is the true one).
* `d(n) = n.divisors.card`; the sum runs over `1 ≤ n ≤ ⌊x⌋`; `O` is `=O[atTop]` on `ℝ`
  (only large `x` matter, so the restriction `x ≥ 2` is immaterial); `γ` is
  `Real.eulerMascheroniConstant`.
* Because `sInf ∅ = 0` and the `sInf` of an unbounded set is `0` in Lean, the equation
  `divisorExponent = 1/4` forces the set to be non-empty, bounded below and with infimum `1/4`,
  i.e. it is exactly the intended statement. -/
def DirichletDivisorProblem : Prop := divisorExponent = 1 / 4

/-- **Known result** (Dirichlet's interchange of summation; e.g. Apostol, *Introduction to
Analytic Number Theory*, Thm 3.3 proof): `∑_{1 ≤ n ≤ N} d(n) = ∑_{1 ≤ d ≤ N} ⌊N/d⌋`. -/
theorem sum_card_divisors_eq_sum_div (N : ℕ) :
    ∑ n ∈ Icc 1 N, n.divisors.card = ∑ d ∈ Icc 1 N, N / d := by
  have h1 : ∀ n ∈ Icc 1 N, n.divisors.card = ∑ d ∈ Icc 1 N, if d ∣ n then 1 else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    rw [← card_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Icc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
    · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← card_filter, show Icc 1 N = Icc (0 + 1) N from rfl, Finset.Icc_add_one_left_eq_Ioc,
    Nat.Ioc_filter_dvd_card_eq_div]

/-- **Known result** (trivial bound; Apostol, Thm 3.3 weakened): `|Δ(x)| ≤ 2x` for `x ≥ 1`. -/
theorem abs_divisorDelta_le {x : ℝ} (hx : 1 ≤ x) : |divisorDelta x| ≤ 2 * x := by
  set N := ⌊x⌋₊ with hN
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hS : (∑ n ∈ Icc 1 N, ((n.divisors.card : ℕ) : ℝ)) = ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) (sum_card_divisors_eq_sum_div N)
  have hup : ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) ≤ ∑ d ∈ Icc 1 N, x * (d : ℝ)⁻¹ := by
    refine sum_le_sum fun d _ => ?_
    rw [← Nat.floor_div_natCast, ← div_eq_mul_inv]
    exact Nat.floor_le (div_nonneg hx0 (Nat.cast_nonneg _))
  have hlo : ∑ d ∈ Icc 1 N, (x * (d : ℝ)⁻¹ - 1) ≤ ∑ d ∈ Icc 1 N, ((N / d : ℕ) : ℝ) := by
    refine sum_le_sum fun d _ => ?_
    rw [← Nat.floor_div_natCast, ← div_eq_mul_inv]
    linarith [Nat.lt_floor_add_one (x / d)]
  have hsumx : ∑ d ∈ Icc 1 N, x * (d : ℝ)⁻¹ = x * ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; rw [mul_sum]
  rw [sum_sub_distrib, hsumx] at hlo
  rw [hsumx] at hup
  simp only [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one] at hlo
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hl1 := log_le_harmonic_floor x hx0
  have hl2 := harmonic_floor_le_one_add_log x hx
  rw [← hN] at hl1 hl2
  have hg1 := Real.one_half_lt_eulerMascheroniConstant
  have hg2 := Real.eulerMascheroniConstant_lt_two_thirds
  have e1 : x * Real.log x ≤ x * ((harmonic N : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hl1 hx0
  have e2 : x * ((harmonic N : ℚ) : ℝ) ≤ x * (1 + Real.log x) := mul_le_mul_of_nonneg_left hl2 hx0
  unfold divisorDelta
  rw [← hN, hS, abs_le]
  constructor <;> nlinarith

/-- **Known result**: `Δ(x) = O(x)`. -/
theorem divisorDelta_isBigO_self : divisorDelta =O[atTop] fun x : ℝ => x := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]
  exact abs_divisorDelta_le hx

/-- **Known result**: the exponent `a = 1` is admissible (so the set defining `α₂` is
non-empty).  This is far from the known `α₂ ≤ 131/416` (Huxley) and is no progress on the
open problem. -/
theorem one_mem_divisorExponentSet : (1 : ℝ) ∈ divisorExponentSet := by
  intro ε hε
  refine divisorDelta_isBigO_self.trans ?_
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ x),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-! ## Problem 374: the Piltz divisor problem -/

/-- `d_k(n)`: the number of ordered `k`-tuples of positive integers with product `n`
(for `n ≥ 1` every entry of such a tuple is a divisor of `n`). -/
def piltzD (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k => n.divisors).filter fun f => ∏ i, f i = n).card

/-- The Piltz main term `Res_{s=1} (ζ(s)^k x^s / s)`, written as
`(2πi)⁻¹ ∮_{|s-1| = 1/2} ζ(s)^k x^s / s ds`. -/
noncomputable def piltzMainTerm (k : ℕ) (x : ℝ) : ℂ :=
  (2 * π * Complex.I)⁻¹ •
    ∮ s in C(1, 1 / 2), riemannZeta s ^ k * (x : ℂ) ^ s / s

/-- `Δ_k(x) = ∑_{n ≤ x} d_k(n) - Res_{s=1}(ζ(s)^k x^s / s)` (a complex number; it is real). -/
noncomputable def piltzDelta (k : ℕ) (x : ℝ) : ℂ :=
  ((∑ n ∈ Icc 1 ⌊x⌋₊, piltzD k n : ℕ) : ℂ) - piltzMainTerm k x

/-- `α_k = inf {a : ∀ ε > 0, Δ_k(x) = O_{k,ε}(x^{a+ε})}`. -/
noncomputable def piltzExponent (k : ℕ) : ℝ :=
  sInf {a : ℝ | ∀ ε > 0, piltzDelta k =O[atTop] fun x : ℝ => x ^ (a + ε)}

/-- **Problem 374 (OPEN).**  ProofAtlas `exactTarget`:

> "For each integer k>=3, let d_k(n) count the ordered k-tuples of positive integers with
> product n, and let Delta_k(x)=sum_{n<=x} d_k(n)-Res_{s=1}(zeta(s)^k x^s/s). Determine
> alpha_k=inf{a: for every epsilon>0, Delta_k(x)=O_{k,epsilon}(x^(a+epsilon)) as x tends to
> infinity}."

Modelling choices:
* "Determine `α_k`" is rendered as the standard Piltz conjecture `α_k = (k-1)/(2k)` for every
  `k ≥ 3` (the value `α_k ≥ (k-1)/(2k)` is known; equality is open for every `k ≥ 3`).
* The residue is the contour integral `piltzMainTerm` (see the gap note in the module doc).
* `O` is `=O[atTop]` on `ℝ`, with the complex-valued `Δ_k` measured by its norm; `k` is fixed,
  so `O_{k,ε}` is `O_ε` for each `k`.
* The `sInf` junk values (`0`) never equal `(k-1)/(2k) > 0`, so the equation is faithful. -/
def PiltzDivisorProblem : Prop :=
  ∀ k : ℕ, 3 ≤ k → piltzExponent k = ((k : ℝ) - 1) / (2 * k)

/-- **Known result** (definitional consistency): `d_2(n) = d(n)`. -/
theorem piltzD_two (n : ℕ) : piltzD 2 n = n.divisors.card := by
  rw [← card_map ⟨fun d => (d, n / d), fun _ _ => congr_arg Prod.fst⟩, Nat.map_div_right_divisors, piltzD]
  refine card_nbij' (fun f => (f 0, f 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq, Fin.prod_univ_two] at hf
    simp only [mem_coe, Nat.mem_divisorsAntidiagonal]
    exact ⟨hf.2, (Nat.mem_divisors.1 (hf.1 0)).2⟩
  · intro p hp
    simp only [mem_coe, Nat.mem_divisorsAntidiagonal] at hp
    simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq, Fin.prod_univ_two]
    refine ⟨fun i => ?_, by simpa using hp.1⟩
    fin_cases i
    · exact Nat.mem_divisors.2 ⟨⟨p.2, hp.1.symm⟩, hp.2⟩
    · exact Nat.mem_divisors.2 ⟨⟨p.1, by rw [← hp.1]; simp [mul_comm]⟩, hp.2⟩
  · intro f _
    ext i; fin_cases i <;> rfl
  · intro p _; rfl

/-! ## Problem 230: the Gauss circle problem -/

/-- `N(r) = #{(a, b) ∈ ℤ² : a² + b² ≤ r²}`, the lattice points in the closed disc of radius
`r` centred at the origin. -/
noncomputable def gaussCount (r : ℝ) : ℕ :=
  Nat.card {p : ℤ × ℤ | ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ r ^ 2)}

/-- `E(r) = N(r) - π r²`. -/
noncomputable def gaussError (r : ℝ) : ℝ := gaussCount r - π * r ^ 2

/-- **Problem 230 (OPEN).**  ProofAtlas `exactTarget`:

> "Determine the sharp order of the error term E(r) in N(r) = pi*r^2 + E(r), where N(r) counts
> the integer lattice points in the disk of radius r centered at the origin; in particular,
> prove or disprove that E(r) = O(r^(1/2+eps)) for every eps > 0."

Modelling choices:
* Only the explicit "in particular" statement is formalised: `∀ ε > 0, E(r) = O(r^{1/2+ε})`
  as `r → ∞` (Hardy's conjecture).  "Determine the sharp order" is not a proposition.
* The disc is closed (`a² + b² ≤ r²`); `O` is `=O[atTop]` on `ℝ`; `N(r)` is `Nat.card` of a
  set that is finite for every `r`. -/
def GaussCircleProblem : Prop :=
  ∀ ε > 0, gaussError =O[atTop] fun r : ℝ => r ^ ((1 : ℝ) / 2 + ε)

/-! ## Problem 181: Waring's function `G(k)` -/

/-- `s` is admissible for `G(k)`: every sufficiently large `N` is a sum of exactly `s`
non-negative `k`-th powers (equivalently, of at most `s` positive `k`-th powers). -/
def IsWaringBound (k s : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ x : Fin s → ℕ, ∑ i, x i ^ k = N

/-- `G(k)`: the least admissible `s` (junk `0` if none existed; Hilbert's theorem, not in
Mathlib, says one exists). -/
noncomputable def waringG (k : ℕ) : ℕ := sInf {s | IsWaringBound k s}

/-- **Problem 181 (OPEN).**  ProofAtlas `exactTarget`:

> "For each integer k>=3, let G(k) be the least positive integer s for which every sufficiently
> large positive integer N is expressible as a sum of at most s positive integral k-th powers.
> Determine the entire function G(k) for all k>=3. Equivalently, zeros may be allowed and
> exactly s nonnegative integral k-th powers used; this is not the condition of exactly s
> positive summands."

Modelling choices:
* "Determine the entire function `G`" is not a proposition and there is no agreed conjectural
  closed formula for all `k`.  This `Prop` is only the **first open instance**, the standard
  conjecture `G(3) = 4` (known: `4 ≤ G(3) ≤ 7`).  The full problem is not formalised.
* Uses the "exactly `s` non-negative `k`-th powers" form, which the target states is
  equivalent.
* `waringG 3 = 4` forces the admissible set to be non-empty, so the `sInf` junk value does not
  enter. -/
def WaringGThreeProblem : Prop := waringG 3 = 4

/-- **Known result** (Lagrange 1770, via Mathlib's `Nat.sum_four_squares`): every `N` is a sum
of four squares. -/
theorem isWaringBound_two_four : IsWaringBound 2 4 := by
  refine ⟨0, fun N _ => ?_⟩
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares N
  exact ⟨![a, b, c, d], by simpa [Fin.sum_univ_four] using h⟩

/-- **Known result** (Legendre / Gauss; integers `≡ 7 (mod 8)` are not sums of three squares):
three squares do not suffice for all large `N`. -/
theorem not_isWaringBound_two_of_le_three {s : ℕ} (hs : s ≤ 3) : ¬ IsWaringBound 2 s := by
  rintro ⟨N₀, h⟩
  obtain ⟨x, hx⟩ := h (8 * N₀ + 7) (by omega)
  have hc := congrArg (fun n : ℕ => (n : ZMod 8)) hx
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_mul] at hc
  have h8 : ((8 : ℕ) : ZMod 8) = 0 := by decide
  rw [h8, zero_mul, zero_add] at hc
  interval_cases s
  · simp at hc; exact absurd hc (by decide)
  · simp at hc
    generalize (x 0 : ZMod 8) = a at hc; revert a; decide
  · simp [Fin.sum_univ_succ] at hc
    generalize (x 0 : ZMod 8) = a at hc; generalize (x 1 : ZMod 8) = b at hc
    revert a b; decide
  · simp [Fin.sum_univ_succ] at hc
    generalize (x 0 : ZMod 8) = a at hc; generalize (x 1 : ZMod 8) = b at hc
    generalize (x 2 : ZMod 8) = c at hc
    revert a b c; decide

/-- **Known result** (Lagrange + Legendre): `G(2) = 4`. -/
theorem waringG_two : waringG 2 = 4 := by
  apply le_antisymm (Nat.sInf_le isWaringBound_two_four)
  refine le_csInf ⟨4, isWaringBound_two_four⟩ fun s hs => ?_
  by_contra h
  exact not_isWaringBound_two_of_le_three (by omega) hs

/-- **Known result** (classical; cubes are `0, ±1 (mod 9)`, so `N ≡ 4 (mod 9)` is not a sum of
three cubes): every admissible `s` for `k = 3` satisfies `s ≥ 4`, i.e. `G(3) ≥ 4`. -/
theorem four_le_of_isWaringBound_three {s : ℕ} (h : IsWaringBound 3 s) : 4 ≤ s := by
  by_contra hs
  obtain ⟨N₀, h⟩ := h
  obtain ⟨x, hx⟩ := h (9 * N₀ + 4) (by omega)
  have hc := congrArg (fun n : ℕ => (n : ZMod 9)) hx
  simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_add, Nat.cast_mul] at hc
  have h9 : ((9 : ℕ) : ZMod 9) = 0 := by decide
  rw [h9, zero_mul, zero_add] at hc
  interval_cases s
  · simp at hc; exact absurd hc (by decide)
  · simp at hc
    generalize (x 0 : ZMod 9) = a at hc; revert a; decide
  · simp [Fin.sum_univ_succ] at hc
    generalize (x 0 : ZMod 9) = a at hc; generalize (x 1 : ZMod 9) = b at hc
    revert a b; decide
  · simp [Fin.sum_univ_succ] at hc
    generalize (x 0 : ZMod 9) = a at hc; generalize (x 1 : ZMod 9) = b at hc
    generalize (x 2 : ZMod 9) = c at hc
    revert a b c; decide

/-- Fourth powers are `0` or `1` modulo `16`. -/
theorem pow_four_mod_sixteen_le (n : ℕ) : n ^ 4 % 16 ≤ 1 := by
  rw [Nat.pow_mod]
  have : n % 16 < 16 := Nat.mod_lt _ (by norm_num)
  generalize n % 16 = m at this
  interval_cases m <;> norm_num

/-- **Known result** (classical; fourth powers are `0, 1 (mod 16)`, so `N ≡ 15 (mod 16)` needs
at least 15 fourth powers): every admissible `s` for `k = 4` satisfies `s ≥ 15`.  (The sharp
`G(4) = 16`, Davenport 1939, is not formalised here.) -/
theorem fifteen_le_of_isWaringBound_four {s : ℕ} (h : IsWaringBound 4 s) : 15 ≤ s := by
  by_contra hs
  obtain ⟨N₀, h⟩ := h
  obtain ⟨x, hx⟩ := h (16 * N₀ + 15) (by omega)
  have h1 : (∑ i, x i ^ 4) % 16 = (∑ i, x i ^ 4 % 16) % 16 := Finset.sum_nat_mod _ _ _
  have h2 : ∑ i, x i ^ 4 % 16 ≤ ∑ _i : Fin s, 1 := Finset.sum_le_sum fun i _ => pow_four_mod_sixteen_le _
  simp at h2
  rw [hx] at h1
  omega

end CryptoLean.OpenProblems.NumberTheory.LatticeDivisor

#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.sum_card_divisors_eq_sum_div
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.abs_divisorDelta_le
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.divisorDelta_isBigO_self
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.one_mem_divisorExponentSet
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.piltzD_two
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.isWaringBound_two_four
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.not_isWaringBound_two_of_le_three
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.waringG_two
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.four_le_of_isWaringBound_three
#print axioms CryptoLean.OpenProblems.NumberTheory.LatticeDivisor.fifteen_le_of_isWaringBound_four
