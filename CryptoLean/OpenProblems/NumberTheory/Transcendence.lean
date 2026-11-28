import Mathlib

/-!
# Open problems in transcendence and irrationality theory

ProofAtlas problems (releaseRank) 26, 163, 165, 251, 316, 421, 458.

**All seven problems are OPEN** (problem 165 is recorded by ProofAtlas as
`open_disputed_claim`: a claimed proof exists but is not accepted).  Each appears below
only as an unproved `def … : Prop` whose docstring quotes the ProofAtlas `exactTarget` and
lists the modelling choices.  Nothing in this file proves, or claims progress towards, any
of them.

Mathlib objects reused (no re-definitions):
* `Transcendental`, `IsAlgebraic`, `AlgebraicIndependent`, `Algebra.trdeg`,
  `IntermediateField.adjoin`, `LinearIndependent`;
* `Real.exp`, `Complex.exp`, `Real.pi`, `Real.Gamma`, `Real.rpow`;
* `riemannZeta` and `zeta_nat_eq_tsum_of_gt_one`;
* `Real.eulerMascheroniConstant` and `Real.tendsto_harmonic_sub_log`;
* `Liouville`, `liouvilleNumber`, `transcendental_liouvilleNumber`, `irrational_pi`.

## What is missing from Mathlib (gap notes)

* **Transcendence of `π` and of `e`** (Lindemann 1882, Hermite 1873), and more generally the
  Lindemann–Weierstrass theorem: Mathlib only has the analytic part
  (`Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`), not the theorem.
  Consequently the known result "at least one of `e + π`, `e·π` is transcendental" is proved
  here only *conditionally* on `Transcendental ℚ π` (`transcendental_add_or_mul_of_pi`), and
  the hypothesis is not discharged.
* **Irrationality of `e`** is not in Mathlib and is not formalised here.
* **Apéry's theorem** (`ζ(3)` irrational) and **Ball–Rivoal / Zudilin** (infinitely many
  odd zeta values irrational; one of `ζ(5), ζ(7), ζ(9), ζ(11)` irrational) are not in Mathlib
  and are not formalised here.
* **The six exponentials theorem** (Lang, Ramachandra), the known weakening of problem 316,
  is not in Mathlib and is not formalised here.
* **Gauss's multiplication formula** for `Γ` (general `n`) is not in Mathlib (only reflection
  `Real.Gamma_mul_Gamma_one_sub` and the duplication formula), so for problem 458 only the
  reflection generators are checked to give algebraic values (`reflection_gammaMonomial_isAlgebraic`).
* **Schanuel ⇒ algebraic independence of `e` and `π`** (a known implication, via
  `z₁ = 1, z₂ = iπ`) is *not* formalised here: it needs a transcendence-degree argument
  transferring independence of `(e, iπ)` to `(e, π)` that was not completed (reported as
  dropped).

## Known results proved here (all reuse Mathlib)

* `transcendental_liouvilleNumber_rat`: Liouville's constants are transcendental over `ℚ`.
* `irrational_pi'`: `π` is irrational (Lambert).
* `transcendental_add_or_mul`: if `x` is transcendental, then for every `y` one of `x + y`,
  `x·y` is transcendental; `transcendental_add_or_mul_of_pi`: the `e, π` instance, conditional
  on the (known, not-in-Mathlib) transcendence of `π`.
* `ePiAlgebraicIndependence_iff`: the quoted problem 163 is Mathlib's
  `AlgebraicIndependent ℚ ![exp 1, π]`.
* `zetaSeries_three_eq`, `zetaSeries_five_eq`: the series in problems 165/421 are
  `riemannZeta 3`, `riemannZeta 5`; `zetaThreeTranscendence_iff_complex` and
  `zetaFiveIrrationality_iff_complex` restate problems 165/421 via `riemannZeta`.
* `tendsto_harmonic_sub_log_eq_gamma`, `eulerGamma_mem_Ioo`: Mathlib's `γ` is the quoted
  limit and `1/2 < γ < 2/3`.
* `reflection_gammaMonomial_isAlgebraic`: the reflection generators of problem 458 do give
  algebraic values (Euler reflection + Niven-type algebraicity of `sin(qπ)`).
-/

namespace CryptoLean.OpenProblems.NumberTheory.Transcendence

open Complex
open scoped Real

/-! ## Problem 26: Schanuel's conjecture -/

/-- **Open problem** (ProofAtlas releaseRank 26, *Schanuel's conjecture*). Quoted exactTarget:
"Prove or disprove that if z_1,...,z_n in C are linearly independent over Q, then the field
Q(z_1,...,z_n,e^{z_1},...,e^{z_n}) has transcendence degree at least n over Q."

Modelling choices:
* `z : Fin n → ℂ`, linear independence is Mathlib's `LinearIndependent ℚ z`;
* the field is `IntermediateField.adjoin ℚ (range z ∪ range (exp ∘ z))` inside `ℂ`;
* transcendence degree is Mathlib's `Algebra.trdeg ℚ` (a cardinal), compared with `n`.

This is OPEN; it is not proved here. -/
def SchanuelConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    (n : Cardinal) ≤
      Algebra.trdeg ℚ
        (IntermediateField.adjoin ℚ (Set.range z ∪ Set.range (fun i => Complex.exp (z i))))

/-! ## Problem 163: algebraic independence of `e` and `π` -/

/-- **Open problem** (ProofAtlas releaseRank 163, *Algebraic independence of e and pi*).
Quoted exactTarget: "Prove that no nonzero polynomial P in Q[X,Y] satisfies P(e,pi)=0."

Modelling choices: `Q[X,Y]` is `MvPolynomial (Fin 2) ℚ` (variable `0` is `X`, `1` is `Y`),
`e = Real.exp 1`, `pi = Real.pi`, evaluation is `MvPolynomial.aeval` into `ℝ`.

This is OPEN; it is not proved here.  `ePiAlgebraicIndependence_iff` shows it is Mathlib's
`AlgebraicIndependent ℚ ![Real.exp 1, π]`. -/
def EPiAlgebraicIndependence : Prop :=
  ∀ P : MvPolynomial (Fin 2) ℚ, P ≠ 0 → MvPolynomial.aeval ![Real.exp 1, π] P ≠ 0

/-- The quoted statement of problem 163 is Mathlib's algebraic independence of `(e, π)`
over `ℚ` (definitional unfolding via `algebraicIndependent_iff`). -/
theorem ePiAlgebraicIndependence_iff :
    EPiAlgebraicIndependence ↔ AlgebraicIndependent ℚ ![Real.exp 1, π] := by
  rw [algebraicIndependent_iff]
  constructor
  · intro h P hP
    by_contra hne
    exact h P hne hP
  · intro h P hne hP
    exact hne (h P hP)

/-! ## Problem 165: transcendence of `ζ(3)` -/

/-- **Open problem** (ProofAtlas releaseRank 165, *Transcendence of Apery's Constant*; status
`open_disputed_claim`). Quoted exactTarget: "Prove or disprove that the value zeta(3) is
transcendental over the rational numbers."

Modelling choices: `zeta(3)` is the real series `∑' n : ℕ, 1 / n ^ 3` (the `n = 0` term is
`1 / 0 = 0` in Lean, so this is `∑_{n ≥ 1} n⁻³`); `zetaSeries_three_eq` identifies it with
`riemannZeta 3`.  "Prove or disprove" is modelled by stating the positive assertion
`Transcendental ℚ ζ(3)`; its negation is the "disprove" branch.

This is OPEN; it is not proved here (irrationality of `ζ(3)`, Apéry 1979, is known but not in
Mathlib). -/
def ZetaThreeTranscendence : Prop :=
  Transcendental ℚ (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3)

/-! ## Problem 251: irrationality of Euler's constant -/

/-- **Open problem** (ProofAtlas releaseRank 251, *Irrationality of Euler's Constant*).
Quoted exactTarget: "Prove or disprove that Euler's constant gamma = lim_{n->infty}
(1 + 1/2 + ... + 1/n - log n) = 0.5772156649... is irrational."

Modelling choices: `gamma` is Mathlib's `Real.eulerMascheroniConstant`, which
`tendsto_harmonic_sub_log_eq_gamma` shows is the quoted limit; the positive assertion is
stated (its negation is the "disprove" branch).

This is OPEN; it is not proved here. -/
def EulerGammaIrrational : Prop :=
  Irrational Real.eulerMascheroniConstant

/-! ## Problem 316: the four exponentials conjecture -/

/-- **Open problem** (ProofAtlas releaseRank 316, *Four Exponentials Conjecture*). Quoted
exactTarget: "Prove or disprove that, for complex numbers x1, x2 linearly independent over Q
and y1, y2 linearly independent over Q, at least one of the four numbers exp(x_i y_j)
(i, j in {1,2}) is transcendental."

Modelling choices: `x y : Fin 2 → ℂ`, linear independence is `LinearIndependent ℚ`,
transcendence is `Transcendental ℚ` in `ℂ`; the positive assertion is stated.

This is OPEN; it is not proved here (the six exponentials theorem is known but not in
Mathlib). -/
def FourExponentialsConjecture : Prop :=
  ∀ x y : Fin 2 → ℂ, LinearIndependent ℚ x → LinearIndependent ℚ y →
    ∃ i j : Fin 2, Transcendental ℚ (Complex.exp (x i * y j))

/-! ## Problem 421: irrationality of `ζ(5)` -/

/-- **Open problem** (ProofAtlas releaseRank 421, *Irrationality of zeta(5)*). Quoted
exactTarget: "Prove that zeta(5) = sum_{n>=1} 1/n^5 is irrational."

Modelling choices: the sum is the real series `∑' n : ℕ, 1 / n ^ 5` (the `n = 0` term is
`1 / 0 = 0` in Lean); `zetaSeries_five_eq` identifies it with `riemannZeta 5`.

This is OPEN; it is not proved here. -/
def ZetaFiveIrrational : Prop :=
  Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5)

/-! ## Problem 458: Rohrlich's conjecture -/

/-- The value `π^(b/2) · ∏_a Γ(a)^(m_a)` (real `Γ`, real power of `π`, integer powers of
`Γ(a)`). -/
noncomputable def gammaMonomial (b : ℤ) (m : ℚ →₀ ℤ) : ℝ :=
  Real.pi ^ ((b : ℝ) / 2) * m.prod (fun a k => Real.Gamma (a : ℝ) ^ k)

/-- The standard multiplicative relations, written additively as exponent vectors
`(b, m)` for `π^(b/2) ∏ Γ(a)^(m_a)`:
* reflection: for rational `0 < a < 1`, `π^(-1) Γ(a) Γ(1-a) = 1 / sin(π a)`, i.e.
  `(-2, δ_a + δ_{1-a})`;
* multiplication (Gauss, at `x = a / n`, all arguments already in `(0,1)`): for `n ≥ 1` and
  rational `0 < a < 1`,
  `π^(-(n-1)/2) ∏_{k<n} Γ((a+k)/n) · Γ(a)^(-1) = 2^((n-1)/2) n^(1/2-a)`, i.e.
  `(-(n-1), ∑_{k<n} δ_{(a+k)/n} - δ_a)`. -/
def rohrlichStandardRelations : Set (ℤ × (ℚ →₀ ℤ)) :=
  {r | ∃ a : ℚ, 0 < a ∧ a < 1 ∧ r = (-2, Finsupp.single a 1 + Finsupp.single (1 - a) 1)} ∪
  {r | ∃ (n : ℕ) (a : ℚ), 1 ≤ n ∧ 0 < a ∧ a < 1 ∧
      r = (-((n : ℤ) - 1),
        (∑ k ∈ Finset.range n, Finsupp.single ((a + k) / n) 1) - Finsupp.single a 1)}

/-- **Open problem** (ProofAtlas releaseRank 458, *Rohrlich Conjecture on Multiplicative
Relations among Gamma Values at Rational Points*). Quoted exactTarget: "Prove or disprove
that every relation pi^(b/2) product_a Gamma(a)^m_a in Qbar, for integers b and finitely
supported integers m_a at rational 0<a<1, follows multiplicatively, modulo nonzero algebraic
factors, from the translation, reflection and multiplication formulas for the classical
gamma function."

Modelling choices:
* `m : ℚ →₀ ℤ` with support in `(0,1)`; `Γ` is `Real.Gamma` (all values are positive reals,
  so "in Qbar" is `IsAlgebraic ℚ` of a real number); the monomial is `gammaMonomial b m`;
* multiplicative relations among monomials are written additively as exponent vectors in
  `ℤ × (ℚ →₀ ℤ)`, and "follows multiplicatively, modulo nonzero algebraic factors" is
  membership in the additive subgroup generated by the exponent vectors of the standard
  relations `rohrlichStandardRelations`;
* the translation formula `Γ(x+1) = xΓ(x)` changes a monomial only by a nonzero rational
  factor, so it is used to move all arguments into `(0,1)`: the multiplication formula is
  taken only at `x = a/n` with `0 < a < 1`, where all arguments `(a+k)/n` lie in `(0,1)`
  (Gauss's formula at other `x` reduces to these by translation);
* the positive assertion is stated (its negation is the "disprove" branch).

This is OPEN; it is not proved here. -/
def RohrlichConjecture : Prop :=
  ∀ (b : ℤ) (m : ℚ →₀ ℤ), (∀ a ∈ m.support, 0 < a ∧ a < 1) →
    IsAlgebraic ℚ (gammaMonomial b m) →
      (b, m) ∈ AddSubgroup.closure rohrlichStandardRelations

/-! ## Known results -/

/-- **Known result** (Liouville 1844; Mathlib `transcendental_liouvilleNumber`): for every
`m ≥ 2`, Liouville's number `∑ m^(-k!)` is transcendental over `ℚ`. -/
theorem transcendental_liouvilleNumber_rat {m : ℕ} (hm : 2 ≤ m) :
    Transcendental ℚ (liouvilleNumber m) := by
  intro h
  exact transcendental_liouvilleNumber hm ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr h)

/-- **Known result** (Lambert 1761; Mathlib `irrational_pi`): `π` is irrational. -/
theorem irrational_pi' : Irrational π := irrational_pi

/-- **Known result** (elementary): if `x` is transcendental over `ℚ`, then for every `y` at
least one of `x + y`, `x * y` is transcendental (otherwise `x` is a root of
`X² - (x+y)X + xy`, whose coefficients are algebraic). -/
theorem transcendental_add_or_mul {A : Type*} [Field A] [CharZero A] {x : A}
    (hx : Transcendental ℚ x) (y : A) :
    Transcendental ℚ (x + y) ∨ Transcendental ℚ (x * y) := by
  by_contra h
  rw [not_or, Transcendental, Transcendental, not_not, not_not] at h
  obtain ⟨hs, hp⟩ := h
  have hd : IsAlgebraic ℚ ((x - y) ^ 2) := by
    have : (x - y) ^ 2 = (x + y) ^ 2 - (4 : ℚ) • (x * y) := by
      rw [show ((4 : ℚ) • (x * y)) = 4 * (x * y) by norm_num [Algebra.smul_def]]; ring
    rw [this]
    exact (hs.pow 2).sub (hp.smul 4)
  have h2 : IsAlgebraic ℚ (x - y) := hd.of_pow (by norm_num)
  apply hx
  have : x = (2⁻¹ : ℚ) • ((x + y) + (x - y)) := by
    rw [Algebra.smul_def, map_inv₀, map_ofNat]; field_simp; ring
  rw [this]
  exact (hs.add h2).smul _

/-- **Known result, conditional form** (the hypothesis is Lindemann's 1882 theorem, which is
not in Mathlib): if `π` is transcendental then at least one of `e + π`, `e·π` is
transcendental. -/
theorem transcendental_add_or_mul_of_pi (hπ : Transcendental ℚ π) :
    Transcendental ℚ (Real.exp 1 + π) ∨ Transcendental ℚ (Real.exp 1 * π) := by
  rw [add_comm, mul_comm]
  exact transcendental_add_or_mul hπ _

/-- **Known result** (Mathlib `zeta_nat_eq_tsum_of_gt_one`): the series of problem 165 is
`ζ(3)`. -/
theorem zetaSeries_three_eq :
    (((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 3 : ℝ)) : ℂ) = riemannZeta 3 := by
  rw [show (3 : ℂ) = ((3 : ℕ) : ℂ) by norm_num, zeta_nat_eq_tsum_of_gt_one (by norm_num),
    Complex.ofReal_tsum]
  push_cast
  rfl

/-- **Known result** (Mathlib `zeta_nat_eq_tsum_of_gt_one`): the series of problem 421 is
`ζ(5)`. -/
theorem zetaSeries_five_eq :
    (((∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 5 : ℝ)) : ℂ) = riemannZeta 5 := by
  rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_num, zeta_nat_eq_tsum_of_gt_one (by norm_num),
    Complex.ofReal_tsum]
  push_cast
  rfl

/-- Problem 165 restated with Mathlib's `riemannZeta`. -/
theorem zetaThreeTranscendence_iff_complex :
    ZetaThreeTranscendence ↔ Transcendental ℚ (riemannZeta 3) := by
  rw [ZetaThreeTranscendence, ← zetaSeries_three_eq]
  exact (transcendental_algebraMap_iff (A := ℂ) (R := ℚ) (S := ℝ)
    RCLike.ofReal_injective).symm

/-- Problem 421 restated with Mathlib's `riemannZeta`. -/
theorem zetaFiveIrrational_iff_complex :
    ZetaFiveIrrational ↔ ∀ q : ℚ, riemannZeta 5 ≠ (q : ℂ) := by
  rw [ZetaFiveIrrational, ← zetaSeries_five_eq]
  simp only [Irrational, Set.mem_range, not_exists]
  refine forall_congr' fun q => ?_
  rw [← Complex.ofReal_ratCast, ne_eq, Complex.ofReal_inj, eq_comm]

/-- **Known result** (Mathlib `Real.tendsto_harmonic_sub_log`): Mathlib's
`eulerMascheroniConstant` is the limit `lim (1 + 1/2 + ⋯ + 1/n - log n)` of problem 251. -/
theorem tendsto_harmonic_sub_log_eq_gamma :
    Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log n) Filter.atTop
      (nhds Real.eulerMascheroniConstant) :=
  Real.tendsto_harmonic_sub_log

/-- **Known result** (Mathlib `Real.one_half_lt_eulerMascheroniConstant`,
`Real.eulerMascheroniConstant_lt_two_thirds`): `1/2 < γ < 2/3`. -/
theorem eulerGamma_mem_Ioo : Real.eulerMascheroniConstant ∈ Set.Ioo (1 / 2 : ℝ) (2 / 3) :=
  ⟨Real.one_half_lt_eulerMascheroniConstant, Real.eulerMascheroniConstant_lt_two_thirds⟩

/-- **Known result** (Euler's reflection formula, Mathlib `Real.Gamma_mul_Gamma_one_sub`, and
the algebraicity of `sin(qπ)` for rational `q`, Mathlib `Real.isAlgebraic_sin_rat_mul_pi`):
each reflection generator of problem 458 gives an algebraic value,
`π^(-1) Γ(a) Γ(1-a) = 1 / sin(π a) ∈ Q̄`.  (Sanity check that the hypothesis of
`RohrlichConjecture` is satisfiable.) -/
theorem reflection_gammaMonomial_isAlgebraic {a : ℚ} (ha0 : 0 < a) (ha1 : a < 1) :
    IsAlgebraic ℚ (gammaMonomial (-2) (Finsupp.single a 1 + Finsupp.single (1 - a) 1)) := by
  rw [gammaMonomial, Finsupp.prod_add_index (by simp) ?_, Finsupp.prod_single_index (by simp),
    Finsupp.prod_single_index (by simp)]
  · have hpi : Real.pi ^ (((-2 : ℤ) : ℝ) / 2) = π⁻¹ := by
      rw [show (((-2 : ℤ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
    rw [hpi, zpow_one, zpow_one, Rat.cast_sub, Rat.cast_one, Real.Gamma_mul_Gamma_one_sub,
      ← mul_div_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_div, mul_comm]
    exact ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp (Real.isAlgebraic_sin_rat_mul_pi a)).inv
  · intro b hb k l
    have hb' : 0 < (b : ℝ) := by
      rcases Finset.mem_union.mp hb with h | h
      · have := Finsupp.support_single_subset h; simp at this; subst this; exact_mod_cast ha0
      · have := Finsupp.support_single_subset h; simp at this; subst this
        have : (0 : ℚ) < 1 - a := by linarith
        exact_mod_cast this
    exact zpow_add₀ (Real.Gamma_pos_of_pos hb').ne' _ _

end CryptoLean.OpenProblems.NumberTheory.Transcendence

#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.ePiAlgebraicIndependence_iff
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.transcendental_liouvilleNumber_rat
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.irrational_pi'
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.transcendental_add_or_mul
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.transcendental_add_or_mul_of_pi
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.zetaSeries_three_eq
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.zetaSeries_five_eq
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.zetaThreeTranscendence_iff_complex
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.zetaFiveIrrational_iff_complex
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.tendsto_harmonic_sub_log_eq_gamma
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.eulerGamma_mem_Ioo
#print axioms CryptoLean.OpenProblems.NumberTheory.Transcendence.reflection_gammaMonomial_isAlgebraic
