import Mathlib

/-!
# Open problems about the Riemann zeta function and Dirichlet / Dedekind L-functions

ProofAtlas problems (releaseRank) 2, 10, 12, 71, 76, 115, 154, 287, 454.

**All nine problems are OPEN.** Each appears below only as an unproved `def … : Prop`
whose docstring quotes the ProofAtlas `exactTarget` and lists the modelling choices.
Nothing in this file proves, or claims progress towards, any of them.

Mathlib objects reused (no re-definitions):
* `riemannZeta` (the meromorphically continued zeta function; junk value at `s = 1`),
  `RiemannHypothesis`, `riemannZetaZeros`, `riemannZeta_ne_zero_of_one_le_re`,
  `riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_one_sub` (functional equation),
  `riemannZeta_conj`;
* `DirichletCharacter`, `DirichletCharacter.IsPrimitive`, `DirichletCharacter.LFunction`
  (the analytic continuation of `∑ χ(n) n^{-s}`, see `LFunction_eq_LSeries`),
  `DirichletCharacter.LFunction_ne_zero_of_one_le_re`;
* `NumberField.dedekindZeta` (only as the Dirichlet series, see the gap note below);
* `analyticOrderNatAt` (multiplicity of a zero).

## What is missing from Mathlib (gap notes)

* **Analytic continuation of the Dedekind zeta function** (Hecke).  Mathlib's
  `NumberField.dedekindZeta K s` is the `LSeries` `∑ a_n n^{-s}`, which is the junk value `0`
  where the series does not converge, so it is *not* the continued function in the critical
  strip.  Problem 12 is therefore stated by quantifying over every holomorphic function on
  `ℂ ∖ {1}` agreeing with `dedekindZeta K` on `Re s > 1`; by the identity theorem there is at
  most one such function, and by Hecke's theorem (not in Mathlib) there is exactly one, so
  the statement is equivalent to the quoted one.  Hecke's continuation itself is the missing
  ingredient.
* **ζ(1/2) ≠ 0** (the conductor-one case of problem 287, a known result: `ζ(σ) < 0` for
  `0 < σ < 1`, via the alternating eta series) is not in Mathlib and is *not* formalised here.

## Known results proved here (all reuse Mathlib)

* `re_pos_of_riemannZeta_eq_zero`, `mem_criticalStrip_of_nontrivial_zero`: nontrivial zeros of
  `ζ` lie in the open critical strip `0 < Re s < 1`.
* `riemannHypothesisStrip_iff`: the quoted RH (problem 2) is equivalent to Mathlib's
  `RiemannHypothesis`.
* `riemannHypothesisStrip_iff_no_zero_right_half`: RH ⇔ no zeros with `1/2 < Re s < 1`.
* `riemannZeta_one_sub_eq_zero`, `riemannZeta_conj_eq_zero`: the zeros in the critical strip
  are symmetric under `s ↦ 1 - s` and `s ↦ conj s`.
* `riemannZeta_trivial_zero`, `riemannZeta_ne_zero_one_le_re`,
  `dirichletLFunction_ne_zero_one_le_re`: trivial zeros, and non-vanishing on `Re s ≥ 1`.
* `GRHDirichlet.riemannHypothesisStrip`: GRH for Dirichlet L-functions implies RH
  (an implication between open statements, not progress on either).
* `stripZeros_finite`: only finitely many zeros in each bounded box (so the counts used in
  problems 71 and 115 are counts of finite sets).
-/

namespace CryptoLean.OpenProblems.NumberTheory.Zeta

open Complex
open scoped Real

/-! ## Basic facts about the zeros of ζ (known results) -/

/-- **Known result** (Riemann 1859, functional equation; Mathlib's `riemannZeta_one_sub`):
a zero of `ζ` that is not a trivial zero `-2, -4, …` has positive real part. -/
theorem re_pos_of_riemannZeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hre
  push Not at hre
  set t : ℂ := 1 - s with ht
  have hs : s = 1 - t := by rw [ht]; ring
  have htre : 1 ≤ t.re := by simp [ht]; linarith
  have hs0 : s ≠ 0 := by rintro rfl; norm_num [riemannZeta_zero] at hz
  have ht1 : t ≠ 1 := by intro h; apply hs0; rw [hs, h]; ring
  have htn : ∀ n : ℕ, t ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  have hfe := riemannZeta_one_sub htn ht1
  rw [← hs, hz] at hfe
  have h2π : (2 * (π : ℂ)) ^ (-t) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h; exfalso
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact (mul_ne_zero two_ne_zero this) h
  have hΓ : Gamma t ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
  have hcos : cos (π * t / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2π) hΓ) hc) hζ)
      hfe.symm
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hcos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have htk : t = 2 * k + 1 := by
    have := hk
    field_simp at this
    exact this
  have hsk : s = -2 * k := by rw [hs, htk]; ring
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have := congrArg Complex.re hsk
    simp at this
    have : (k : ℝ) < 0 := by exact_mod_cast hk0
    linarith
  · exact hs0 (by simpa using hsk)
  · apply htriv
    refine ⟨(k - 1).toNat, ?_⟩
    rw [hsk]
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    have h' : (((k - 1).toNat : ℕ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by exact_mod_cast this
    rw [h']; push_cast; ring


/-- **Known result** (Riemann 1859; Hadamard and de la Vallée Poussin 1896): every nontrivial
zero of `ζ` (a zero other than `-2, -4, -6, …`; `s = 1` excluded because `riemannZeta 1` is a
junk value) lies in the open critical strip `0 < Re s < 1`. -/
theorem mem_criticalStrip_of_nontrivial_zero {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 := by
  refine ⟨re_pos_of_riemannZeta_eq_zero hz htriv, ?_⟩
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-- **Known result** (Riemann 1859): `ζ(-2n) = 0` for `n = 1, 2, …` (the trivial zeros).
Restatement of Mathlib's `riemannZeta_neg_two_mul_nat_add_one`. -/
theorem riemannZeta_trivial_zero (n : ℕ) : riemannZeta (-2 * (n + 1)) = 0 :=
  riemannZeta_neg_two_mul_nat_add_one n

/-- **Known result** (Hadamard; de la Vallée Poussin 1896): `ζ(s) ≠ 0` for `Re s ≥ 1`.
Mathlib's `riemannZeta_ne_zero_of_one_le_re`. -/
theorem riemannZeta_ne_zero_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- **Known result** (Dirichlet 1837 at `s = 1`; de la Vallée Poussin 1896 on `Re s = 1`):
for every Dirichlet character `χ` mod `q ≥ 1`, `L(s, χ) ≠ 0` for `Re s ≥ 1`, except at the pole
`s = 1` of the principal character. Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re`. -/
theorem dirichletLFunction_ne_zero_one_le_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) : χ.LFunction s ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs

/-- **Known result** (Riemann 1859, functional equation): zeros of `ζ` in the open critical
strip are symmetric under `s ↦ 1 - s`. -/
theorem riemannZeta_one_sub_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - s) = 0 := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  rw [riemannZeta_one_sub hn hs1, hz, mul_zero]

/-- **Known result** (Schwarz reflection; Mathlib's `riemannZeta_conj`): the zeros of `ζ` are
symmetric under complex conjugation. -/
theorem riemannZeta_conj_eq_zero {s : ℂ} (hz : riemannZeta s = 0) :
    riemannZeta ((starRingEnd ℂ) s) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-- **Known result**: for every `T`, there are only finitely many zeros of `ζ` in the box
`0 ≤ Re s ≤ 1`, `|Im s| ≤ T` (zeros of a non-zero meromorphic function are discrete; Mathlib's
`IsCompact.inter_riemannZetaZeros_finite`). -/
theorem stripZeros_finite (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T}.Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset
  rintro ρ ⟨hz, h0, h1, hT⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have := norm_le_abs_re_add_abs_im ρ
  rw [abs_of_nonneg h0] at this
  linarith [le_abs_self T]

/-! ## Problem 2: the Riemann Hypothesis -/

/-- **OPEN (ProofAtlas #2, Riemann Hypothesis).** Quoted exactTarget:

> "For the meromorphic continuation of the Riemann zeta function zeta(s)=sum_{n>=1} n^(-s),
> initially defined for Re(s)>1, every zero s in the open critical strip 0<Re(s)<1 has
> Re(s)=1/2. This is the Riemann Hypothesis for zeta alone; it does not assert simplicity of
> its zeros."

Modelling: `riemannZeta` is Mathlib's continued zeta function (it agrees with
`∑ n^{-s}` for `Re s > 1`, `zeta_eq_tsum_one_div_nat_cpow`). No simplification.
Equivalent to Mathlib's `RiemannHypothesis` (`riemannHypothesisStrip_iff`). -/
def RiemannHypothesisStrip : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → riemannZeta s = 0 → s.re = 1 / 2

/-- **Known result** (equivalence of formulations): the quoted strip form of RH is equivalent
to Mathlib's `RiemannHypothesis` (every zero other than the trivial zeros and the junk point
`s = 1` has real part `1/2`). Uses `mem_criticalStrip_of_nontrivial_zero`. -/
theorem riemannHypothesisStrip_iff : RiemannHypothesisStrip ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htriv _
    obtain ⟨h0, h1⟩ := mem_criticalStrip_of_nontrivial_zero hz htriv
    exact h s h0 h1 hz
  · intro h s h0 h1 hz
    refine h s hz ?_ ?_
    · rintro ⟨n, rfl⟩
      simp at h0
      have : (0:ℝ) ≤ n := n.cast_nonneg
      linarith
    · rintro rfl; simp at h1

/-- **Known result** (equivalence via the functional equation): RH holds iff `ζ` has no zero
with `1/2 < Re s < 1`. -/
theorem riemannHypothesisStrip_iff_no_zero_right_half :
    RiemannHypothesisStrip ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro h s h0 h1 hz
    have := h s (by linarith) h1 hz
    linarith
  · intro h s h0 h1 hz
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exfalso
      refine h (1 - s) (by simp; linarith) (by simp; linarith) ?_
      exact riemannZeta_one_sub_eq_zero h0 h1 hz
    · exact heq
    · exact absurd hz (h s hgt h1)

/-! ## Problem 10: GRH for Dirichlet L-functions -/

/-- **OPEN (ProofAtlas #10, Generalized Riemann Hypothesis for Dirichlet L-functions).**
Quoted exactTarget:

> "For every integer q>=1 and every Dirichlet character chi modulo q, including principal and
> imprimitive characters, every zero s of the meromorphic continuation of
> L(s,chi)=sum_{n>=1}chi(n)n^(-s) in 0<Re(s)<1 satisfies Re(s)=1/2. The continuation is from
> Re(s)>1. Only open-strip zeros are quantified: principal-character poles and boundary zeros
> of imprimitive Euler factors are not counterexamples. No simplicity or central nonvanishing
> requirement is added."

Modelling: `q ≥ 1` is the instance `[NeZero q]`; characters are `DirichletCharacter ℂ q`
(all characters mod `q`, principal and imprimitive included); `DirichletCharacter.LFunction`
is Mathlib's continuation (`LFunction_eq_LSeries` for `Re s > 1`). The only pole (`s = 1`,
principal character) lies outside the open strip. No simplification. -/
def GRHDirichlet : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

/-- **Known result** (implication between open statements, the case `q = 1`): GRH for
Dirichlet L-functions implies RH, since `L(s, χ) = ζ(s)` for the character mod 1
(Mathlib's `DirichletCharacter.LFunction_modOne_eq`). Not progress on either. -/
theorem GRHDirichlet.riemannHypothesisStrip (h : GRHDirichlet) : RiemannHypothesisStrip := by
  intro s h0 h1 hz
  refine h 1 (1 : DirichletCharacter ℂ 1) s h0 h1 ?_
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact hz

/-- GRH for Dirichlet L-functions implies Mathlib's `RiemannHypothesis`. -/
theorem GRHDirichlet.riemannHypothesis (h : GRHDirichlet) : RiemannHypothesis :=
  riemannHypothesisStrip_iff.mp h.riemannHypothesisStrip

/-! ## Problem 12: ERH for Dedekind zeta functions -/

/-- **OPEN (ProofAtlas #12, Extended Riemann hypothesis for Dedekind zeta functions;
ProofAtlas status `open_disputed_claim`).** Quoted exactTarget:

> "For every algebraic number field K (a finite extension of Q, including K=Q), does every zero
> s of its Dedekind zeta function ζ_K(s) in the critical strip 0<Re(s)<1 satisfy Re(s)=1/2?"

Modelling simplifications (see the module gap note):
* Mathlib has no analytic continuation of `NumberField.dedekindZeta`; the continued `ζ_K` is
  represented by an arbitrary `F : ℂ → ℂ` holomorphic on `ℂ ∖ {1}` with `F = dedekindZeta K`
  on `Re s > 1`. Such `F` is unique (identity theorem, `ℂ ∖ {1}` connected) and exists by
  Hecke's theorem (not in Mathlib), so the Prop is equivalent to the quoted statement; without
  Hecke's theorem formalised the existence of `F` is not available in Lean.
* Number fields range over `K : Type` (universe 0); every number field has a model there. -/
def ERHDedekind : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (F : ℂ → ℂ),
    DifferentiableOn ℂ F {1}ᶜ → (∀ s : ℂ, 1 < s.re → F s = NumberField.dedekindZeta K s) →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → F s = 0 → s.re = 1 / 2

/-! ## Problem 76: the Lindelöf hypothesis -/

/-- **OPEN (ProofAtlas #76, The Lindelöf Hypothesis).** Quoted exactTarget:

> "Prove that for every epsilon>0 there is a constant C_epsilon such that
> |zeta(1/2+it)| <= C_epsilon |t|^epsilon for all sufficiently large real |t|."

Modelling: "sufficiently large |t|" is `∃ T₀, ∀ t, T₀ ≤ |t| → …`. No simplification. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-! ## Zero counting with multiplicity (used by problems 71 and 115) -/

/-- Multiplicity of `ρ` as a zero of `ζ` (Mathlib's `analyticOrderNatAt`; `0` at non-zeros). -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- `N(σ, T)`: the number of nontrivial zeros `ρ = β + iγ` (open critical strip) with `β ≥ σ`
and `|γ| ≤ T`, counted with multiplicity. A finite sum by `stripZeros_finite`. -/
noncomputable def zeroCountN (σ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}, zeroMult ρ

/-- The set summed over in `zeroCountN σ T` is finite (**known result**, from
`stripZeros_finite`). -/
theorem zeroCountN_set_finite (σ T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite :=
  (stripZeros_finite T).subset fun _ ⟨hz, h0, h1, _, hT⟩ => ⟨hz, h0.le, h1.le, hT⟩

/-! ## Problem 115: the density hypothesis -/

/-- **OPEN (ProofAtlas #115, Density Hypothesis for Zeroes of the Riemann Zeta Function).**
Quoted exactTarget:

> "Prove that for every sigma with 1/2 <= sigma <= 1 and every epsilon > 0, the number
> N(sigma,T) of nontrivial zeros rho = beta + i gamma of the Riemann zeta function with
> beta >= sigma and |gamma| <= T satisfies N(sigma,T) <= C_{sigma,epsilon}
> T^{2(1-sigma)+epsilon} for all sufficiently large T."

Modelling: nontrivial zeros are the zeros in the open strip `0 < Re ρ < 1` (equivalent by
`mem_criticalStrip_of_nontrivial_zero`); zeros are counted with multiplicity (`zeroCountN`),
the standard convention; "sufficiently large T" is `∃ T₀, ∀ T ≥ T₀`. -/
def DensityHypothesis : Prop :=
  ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (zeroCountN σ T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε)

/-! ## Problem 154: simplicity of the zeros -/

/-- **OPEN (ProofAtlas #154, Simplicity of the Nontrivial Zeros of the Riemann Zeta Function;
status `open_with_solved_subcases`).** Quoted exactTarget:

> "Prove that zeta'(rho) is nonzero for every nontrivial zero rho of the Riemann zeta function;
> equivalently, every nontrivial zero of zeta(s) has multiplicity exactly one."

Modelling: nontrivial zeros are the zeros in the open strip `0 < Re ρ < 1`
(`mem_criticalStrip_of_nontrivial_zero`); `ζ'` is `deriv riemannZeta`. The first ("ζ'(ρ) ≠ 0")
formulation is the one stated. -/
def SimpleZerosConjecture : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → riemannZeta ρ = 0 → deriv riemannZeta ρ ≠ 0

/-! ## Problem 71: Montgomery's pair correlation conjecture -/

/-- The nontrivial zeros of `ζ` with ordinate in `(0, T]`. -/
def zerosUpTo (T : ℝ) : Set ℂ :=
  {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Montgomery's pair count: the number of ordered pairs `(ρ, ρ')` of nontrivial zeros with
ordinates `γ, γ' ∈ (0, T]` and normalized gap `α ≤ (γ - γ') log T / (2π) ≤ β`, each pair
weighted by the product of multiplicities. -/
noncomputable def pairCount (T α β : ℝ) : ℝ :=
  ∑ᶠ p ∈ {p : ℂ × ℂ | p.1 ∈ zerosUpTo T ∧ p.2 ∈ zerosUpTo T ∧
      α ≤ (p.1.im - p.2.im) * Real.log T / (2 * π) ∧
      (p.1.im - p.2.im) * Real.log T / (2 * π) ≤ β},
    ((zeroMult p.1 : ℝ) * zeroMult p.2)

/-- **OPEN (ProofAtlas #71, Montgomery's Pair Correlation Conjecture).** Quoted exactTarget:

> "Prove that normalized vertical gaps between pairs of nontrivial zeros of the Riemann zeta
> function have limiting pair density 1 - (sin(pi u)/(pi u))^2 at fixed positive normalized
> separation."

Modelling (Montgomery 1973 normalization):
* "limiting pair density at positive separation" is stated in integrated form: for all fixed
  `0 < α < β`, `pairCount T α β / ((T / 2π) log T) → ∫_α^β (1 - (sin πu / πu)²) du` as
  `T → ∞`. (Fixed positive `α` excludes the diagonal `δ`-term.)
* Gaps are normalized by `log T / 2π` (the mean spacing at height `T`), ordinates in `(0, T]`.
* Zeros are counted with multiplicity; no RH assumption (ordinates `γ = Im ρ` of all zeros in
  the open strip are used; Montgomery's original paper assumes RH). -/
def PairCorrelationConjecture : Prop :=
  ∀ α β : ℝ, 0 < α → α < β →
    Filter.Tendsto (fun T : ℝ => pairCount T α β / (T / (2 * π) * Real.log T)) Filter.atTop
      (nhds (∫ u in α..β, (1 - (Real.sin (π * u) / (π * u)) ^ 2)))

/-! ## Problem 287: Chowla's central non-vanishing conjecture -/

/-- **OPEN (ProofAtlas #287, Chowla Non-Vanishing Conjecture for Dirichlet L-Functions at the
Central Point; status `open_with_solved_subcases`).** Quoted exactTarget:

> "For every integer q>=1 and every primitive Dirichlet character chi of conductor q, including
> real and nonreal characters and both even and odd parity, the analytically continued
> Dirichlet L-function satisfies L(1/2,chi) != 0. The conductor-one character is included with
> L(s,chi)=zeta(s), whose central value is already known to be nonzero; conductors with no
> primitive characters contribute no cases. No positivity, quantitative lower bound, effective
> constant or off-central zero-free region is part of the assertion."

Modelling: a primitive character of conductor `q` is a `χ : DirichletCharacter ℂ q` with
`χ.IsPrimitive` (`conductor χ = q`); `q ≥ 1` is `[NeZero q]`. No simplification. The known
case `q = 1` (`ζ(1/2) ≠ 0`) is *not* formalised here (missing from Mathlib). -/
def ChowlaCentralNonvanishing : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ.LFunction (1 / 2) ≠ 0

/-! ## Problem 454: linear independence of the zero ordinates -/

/-- `Γ`: the set of distinct positive ordinates of zeros of `ζ` in the open critical strip. -/
def zeroOrdinates : Set ℝ :=
  {γ : ℝ | 0 < γ ∧ ∃ β : ℝ, 0 < β ∧ β < 1 ∧ riemannZeta (β + γ * I) = 0}

/-- **OPEN (ProofAtlas #454, Linear Independence of Distinct Positive Zeta-Zero Ordinates).**
Quoted exactTarget:

> "Let Gamma={gamma>0: zeta(beta+i gamma)=0 for some real beta with 0<beta<1}, as a set of
> distinct real values, not an indexed list counting multiplicities. For every finite set of
> distinct gamma_1,...,gamma_k in Gamma and rational c_1,...,c_k, the equality
> sum_i c_i gamma_i=0 implies c_1=...=c_k=0. No Riemann-hypothesis assumption is imposed."

Modelling: a finite set of distinct elements is an injective family `Fin k → ℝ` with values in
`zeroOrdinates`. No simplification. Equivalent to `LinearIndependent ℚ` of the inclusion
`zeroOrdinates → ℝ` (that equivalence is not proved here). -/
def ZeroOrdinatesLinearIndependence : Prop :=
  ∀ (k : ℕ) (γ : Fin k → ℝ), Function.Injective γ → (∀ i, γ i ∈ zeroOrdinates) →
    ∀ c : Fin k → ℚ, ∑ i, (c i : ℝ) * γ i = 0 → ∀ i, c i = 0

end CryptoLean.OpenProblems.NumberTheory.Zeta

#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.re_pos_of_riemannZeta_eq_zero
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.mem_criticalStrip_of_nontrivial_zero
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannZeta_trivial_zero
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannZeta_ne_zero_one_le_re
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.dirichletLFunction_ne_zero_one_le_re
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannZeta_one_sub_eq_zero
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannZeta_conj_eq_zero
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.stripZeros_finite
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannHypothesisStrip_iff
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.riemannHypothesisStrip_iff_no_zero_right_half
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.GRHDirichlet.riemannHypothesisStrip
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.GRHDirichlet.riemannHypothesis
#print axioms CryptoLean.OpenProblems.NumberTheory.Zeta.zeroCountN_set_finite
