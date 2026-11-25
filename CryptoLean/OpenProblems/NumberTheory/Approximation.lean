import Mathlib

/-!
# Open problems in Diophantine approximation and normality

ProofAtlas problems (releaseRank) 123, 194, 351, 400, 497.

**All five problems are OPEN** (351 and 497 have solved subcases). Each appears below only as
an unproved `def … : Prop` whose docstring quotes the ProofAtlas `exactTarget` and lists the
modelling choices. Nothing in this file proves, or claims progress towards, any of them.

| rank | statement `Prop`            | status |
|------|-----------------------------|--------|
| 123  | `BorelNormalityAlgebraic`   | open   |
| 194  | `EffectiveRoth`             | open   |
| 351  | `MinkowskiConjecture`       | open (solved for `n ≤ 10` in the literature; `n = 1` here) |
| 400  | `PiIsNormal`                | open   |
| 497  | `WirsingConjecture`         | open (solved for `n ≤ 2` in the literature; `n = 1` here) |

Mathlib objects reused: `Real.digits` (our `digit` is shown equal to it on the fractional
part, `digit_eq_real_digits_fract`), `Irrational`, `IsAlgebraic`, `Transcendental`,
`Computable`, `Matrix.det`, `Polynomial.IsPrimitive`, Dirichlet's theorem
(`Real.exists_int_int_abs_mul_sub_le`, `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`),
Liouville's inequality (`Liouville.exists_pos_real_of_irrational_root`).

## What is missing from Mathlib (gap notes)

* Mathlib has no notion of normal number; `IsNormalInBase` is defined here from block
  frequencies. Non-vacuity (existence of a normal number, e.g. Champernowne's constant or
  Borel's almost-everywhere theorem) is **not** formalised.
* **Roth's theorem** (ineffective finiteness of `|α - p/q| < q^(-2-ε)`), Thue–Siegel, and the
  subspace theorem are not in Mathlib and are not formalised here.
* **Minkowski's theorem for `n = 2`** and the higher solved cases (Remak, Dyson, Skubenko,
  McMullen, Hans-Gill–Raka–Sehmi, Kathuria–Raka) are not formalised; only `n = 1`.
* **Wirsing for `n = 2`** (Davenport–Schmidt) and Wirsing's lower bound `w_n^* ≥ (n+1)/2` are
  not formalised; only `n = 1`.

## Known results proved here

* `rat_not_isNormalInBase` — no rational is normal in any base `b ≥ 2`
  (`rat_not_isNormalInBase_ten`, `borel_irrational_hyp_needed`).
* `dirichlet_approximation`, `dirichlet_infinitely_many` — Dirichlet (restated from Mathlib).
* `liouville_inequality` — Liouville's inequality for algebraic irrationals (from Mathlib).
* `minkowskiInDim_one` — the trivial case `n = 1` of Minkowski's conjecture.
* `wirsing_one`, `wirsingConjecture_one` — the case `n = 1` of Wirsing (Dirichlet).
* `wirsingFor_iff` — bridge between the supremum form and the "for every `ε`" form.
-/

open Polynomial Filter Topology Matrix

namespace CryptoLean.OpenProblems.NumberTheory.Approximation

/-! ## Normality -/

/-- The `i`-th digit (`i = 0` is the first digit after the point) of the fractional part of
`x` in base `b`: `⌊x · b^(i+1)⌋ mod b`. -/
noncomputable def digit (b : ℕ) (x : ℝ) (i : ℕ) : ℕ :=
  (⌊x * (b : ℝ) ^ (i + 1)⌋ % (b : ℤ)).toNat

lemma digit_lt {b : ℕ} (hb : 0 < b) (x : ℝ) (i : ℕ) : digit b x i < b := by
  unfold digit
  have h1 := Int.emod_nonneg ⌊x * (b : ℝ) ^ (i + 1)⌋ (b := (b : ℤ)) (by omega)
  have h2 := Int.emod_lt_of_pos ⌊x * (b : ℝ) ^ (i + 1)⌋ (b := (b : ℤ)) (by omega)
  omega

lemma digit_add_int (b : ℕ) (x : ℝ) (t : ℤ) (i : ℕ) :
    digit b (x + t) i = digit b x i := by
  unfold digit
  have : (x + t) * (b : ℝ) ^ (i + 1) = x * (b : ℝ) ^ (i + 1) + ((t * b ^ i * b : ℤ) : ℝ) := by
    push_cast; ring
  rw [this, Int.floor_add_intCast, Int.add_mul_emod_self_right]

lemma digit_shift (b : ℕ) (x : ℝ) (n j : ℕ) :
    digit b x (n + j) = digit b (x * (b : ℝ) ^ n) j := by
  unfold digit
  congr 3
  ring

/-- Number of starting positions `n < N` at which the block `w` occurs in the base-`b` digits
of `x`. -/
noncomputable def blockCount (b : ℕ) (x : ℝ) {k : ℕ} (w : Fin k → Fin b) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => ∀ j : Fin k, digit b x (n + j) = (w j : ℕ)).card

/-- `x` is (simply-and-block) normal in base `b`: every block of `k` digits occurs with
asymptotic frequency `b^(-k)`. -/
def IsNormalInBase (b : ℕ) (x : ℝ) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Fin b),
    Tendsto (fun N : ℕ => (blockCount b x w N : ℝ) / N) atTop (𝓝 (1 / (b : ℝ) ^ k))

lemma digit_ratio (b : ℕ) (p : ℤ) (q : ℕ) (hq : 0 < q) (n j : ℕ) :
    digit b ((p : ℝ) / q) (n + j) =
      digit b ((((p * (b : ℤ) ^ n) % (q : ℤ)).toNat : ℝ) / q) j := by
  rw [digit_shift]
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hnn : 0 ≤ (p * (b : ℤ) ^ n) % (q : ℤ) := Int.emod_nonneg _ (by omega)
  have key : (p : ℝ) / q * (b : ℝ) ^ n =
      (((((p * (b : ℤ) ^ n) % (q : ℤ)).toNat : ℤ) : ℝ) / q) +
        (((p * (b : ℤ) ^ n) / (q : ℤ) : ℤ) : ℝ) := by
    rw [Int.toNat_of_nonneg hnn]
    have := Int.emod_add_mul_ediv (p * (b : ℤ) ^ n) (q : ℤ)
    field_simp
    have h2 : ((p * (b : ℤ) ^ n : ℤ) : ℝ) =
        (((p * (b : ℤ) ^ n) % (q : ℤ) : ℤ) : ℝ) + (q : ℝ) * (((p * (b : ℤ) ^ n) / (q : ℤ) : ℤ) : ℝ) := by
      have h3 := congrArg (fun z : ℤ => (z : ℝ)) this.symm
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at h3
      rw [Int.cast_mul]
      exact h3
    push_cast at h2
    linarith
  rw [key, digit_add_int]
  norm_cast

/-- **Known result** (classical; see e.g. Y. Bugeaud, *Distribution modulo one and Diophantine
approximation*, Cambridge 2012, §4.1): a rational number is not normal in any base `b ≥ 2`
(its digit sequence is eventually periodic). Here: the length-`k` block starting at position
`n` of `p/q` depends only on `p·bⁿ mod q`, so at most `q` blocks of length `q` ever occur,
fewer than the `b^q` possible ones. -/
theorem rat_not_isNormalInBase (r : ℚ) {b : ℕ} (hb : 2 ≤ b) : ¬ IsNormalInBase b (r : ℝ) := by
  intro h
  set q := r.den with hqdef
  have hq : 0 < q := r.den_pos
  have hb0 : 0 < b := by omega
  -- the map from residues to blocks of length `q`
  let g : Fin q → (Fin q → Fin b) := fun s j => ⟨digit b ((s : ℕ) / (q : ℝ)) j, digit_lt hb0 _ _⟩
  have hcard : Fintype.card (Fin q) < Fintype.card (Fin q → Fin b) := by
    simp only [Fintype.card_fin, Fintype.card_fun]
    exact Nat.lt_pow_self (by omega)
  obtain ⟨w, hw⟩ : ∃ w, w ∉ Set.range g := by
    by_contra hcon
    push Not at hcon
    exact absurd (Fintype.card_le_of_surjective g (fun w => hcon w)) (not_le.mpr hcard)
  have hr : (r : ℝ) = (r.num : ℝ) / (q : ℝ) := by
    rw [hqdef]; exact_mod_cast (Rat.num_div_den r).symm
  have hzero : ∀ N, blockCount b (r : ℝ) w N = 0 := by
    intro N
    unfold blockCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n _ hn
    apply hw
    have hlt : ((r.num * (b : ℤ) ^ n) % (q : ℤ)).toNat < q := by
      have h1 := Int.emod_nonneg (r.num * (b : ℤ) ^ n) (b := (q : ℤ)) (by omega)
      have h2 := Int.emod_lt_of_pos (r.num * (b : ℤ) ^ n) (b := (q : ℤ)) (by omega)
      omega
    refine ⟨⟨_, hlt⟩, ?_⟩
    funext j
    apply Fin.ext
    have := hn j
    rw [hr, digit_ratio b r.num q hq n j] at this
    simpa [g] using this
  have ht := h q w
  simp only [hzero, Nat.cast_zero, zero_div] at ht
  have := tendsto_nhds_unique tendsto_const_nhds ht
  have hpos : (0 : ℝ) < 1 / (b : ℝ) ^ q := by positivity
  linarith

/-- Definition sanity check (an instance of `rat_not_isNormalInBase`): no rational number is
normal in base 10. -/
theorem rat_not_isNormalInBase_ten (r : ℚ) : ¬ IsNormalInBase 10 (r : ℝ) :=
  rat_not_isNormalInBase r (by norm_num)

/-- Our `digit` agrees with Mathlib's `Real.digits` applied to the fractional part. -/
theorem digit_eq_real_digits_fract (b : ℕ) [NeZero b] (x : ℝ) (i : ℕ) :
    digit b x i = (Real.digits (Int.fract x) b i : ℕ) := by
  have hx : x = Int.fract x + (⌊x⌋ : ℤ) := by rw [Int.fract]; ring
  rw [hx, digit_add_int]
  unfold digit Real.digits
  have h0 : 0 ≤ Int.fract x * (b : ℝ) ^ (i + 1) := by
    have := Int.fract_nonneg x; positivity
  rw [Fin.val_ofNat, ← Int.floor_toNat, show (Int.fract (Int.fract x + (⌊x⌋ : ℤ))) = Int.fract x
    by simp]
  have hf : 0 ≤ ⌊Int.fract x * (b : ℝ) ^ (i + 1)⌋ := Int.floor_nonneg.mpr h0
  rw [Int.toNat_emod hf (by positivity)]
  simp

/-- **ProofAtlas 123 (OPEN): Borel's normality conjecture for irrational algebraic numbers.**

ProofAtlas `exactTarget` (quoted): "Prove or disprove that every real irrational algebraic
number is normal to every integer base b >= 2."

This `Prop` is the positive ("prove") direction; its negation is the "disprove" direction.
Modelling choices:
* "algebraic" is `IsAlgebraic ℚ x` (equivalently over `ℤ`), "irrational" is `Irrational x`;
* "normal to base `b`" is `IsNormalInBase b x`: every block `w` of `k` digits (any `k`,
  digits `Fin b`) occurs among the first `N` starting positions of the base-`b` expansion of
  the fractional part of `x` with frequency tending to `b^(-k)`. Digits are those of
  `x - ⌊x⌋` (`digit_eq_real_digits_fract`); for negative `x` this is the expansion of the
  fractional part rather than of `|x|`, which does not change normality (the digits of
  `1 - y` are the complements `b - 1 - d` of those of `y`, a bijection on blocks), but this
  equivalence is not formalised here. Overlapping occurrences are counted. -/
def BorelNormalityAlgebraic : Prop :=
  ∀ x : ℝ, IsAlgebraic ℚ x → Irrational x → ∀ b : ℕ, 2 ≤ b → IsNormalInBase b x

/-- The irrationality hypothesis in `BorelNormalityAlgebraic` cannot be dropped:
**Known result** (consequence of `rat_not_isNormalInBase`) — every rational is algebraic and
normal to no base `b ≥ 2`. -/
theorem borel_irrational_hyp_needed (r : ℚ) {b : ℕ} (hb : 2 ≤ b) :
    IsAlgebraic ℚ (r : ℝ) ∧ ¬ IsNormalInBase b (r : ℝ) :=
  ⟨isAlgebraic_algebraMap (R := ℚ) (A := ℝ) r, rat_not_isNormalInBase r hb⟩

/-- **ProofAtlas 400 (OPEN): normality of `π`.**

ProofAtlas `exactTarget` (quoted): "Prove that pi is a normal number: in every integer base
b >= 2, every block of k digits occurs in the base-b expansion of pi with asymptotic frequency
b^{-k}."

Modelling choices: `Real.pi`; "normal in base `b`" is `IsNormalInBase b` (blocks of any length
`k`, overlapping occurrences counted, digits of the fractional part `π - 3`; the integer part
does not affect asymptotic frequencies). -/
def PiIsNormal : Prop :=
  ∀ b : ℕ, 2 ≤ b → IsNormalInBase b Real.pi

/-! ## Rational approximation: known results from Mathlib -/

/-- **Known result** (Dirichlet's approximation theorem, 1842; Mathlib
`Real.exists_int_int_abs_mul_sub_le`): for every real `ξ` and `n ≥ 1` there are integers
`j, k` with `0 < k ≤ n` and `|k ξ - j| ≤ 1/(n+1)`. -/
theorem dirichlet_approximation (ξ : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - ↑j| ≤ 1 / (n + 1) :=
  Real.exists_int_int_abs_mul_sub_le ξ hn

/-- **Known result** (Dirichlet; Mathlib `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`):
an irrational real has infinitely many rational approximations `p/q` (lowest terms) with
`|ξ - p/q| < 1/q²`. -/
theorem dirichlet_infinitely_many {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
  Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ

/-- **Known result** (Liouville's inequality, 1844; Mathlib `Liouville.exists_pos_real_of_irrational_root`):
if an irrational `α` is a root of a nonzero integer polynomial `f` of degree `d`, there is
an effective `c > 0` with `|α - p/q| ≥ c / q^d` for all integers `p` and `q ≥ 1`. -/
theorem liouville_inequality {α : ℝ} (ha : Irrational α) {f : ℤ[X]} (f0 : f ≠ 0)
    (fa : aeval α f = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → c / (q : ℝ) ^ f.natDegree ≤ |α - p / q| := by
  obtain ⟨A, hA, h⟩ := Liouville.exists_pos_real_of_irrational_root ha f0 (by
    rw [eval_map_algebraMap]; exact fa)
  refine ⟨1 / A, by positivity, fun p q hq => ?_⟩
  have := h p (q - 1)
  have hq' : ((q - 1 : ℕ) : ℝ) + 1 = q := by
    rw [Nat.cast_sub (by omega)]; ring
  rw [hq'] at this
  have hqd : (0 : ℝ) < (q : ℝ) ^ f.natDegree := by positivity
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith [abs_nonneg (α - p / q)]

/-! ## ProofAtlas 194: effective Roth -/

/-- Polynomial with integer coefficient list `l = [a₀, a₁, …]` (constant term first). -/
noncomputable def polyOfList (l : List ℤ) : ℤ[X] :=
  ∑ i : Fin l.length, C l[i] * X ^ (i : ℕ)

/-- Rational number encoded as (numerator, denominator). -/
def ratOfPair (r : ℤ × ℕ) : ℚ := r.1 / r.2

/-- An input `(l, a, b, e)` is *valid for `α`*: `polyOfList l` is the integer minimal polynomial
of the real algebraic irrational `α` (primitive, irreducible over `ℤ`, positive leading
coefficient, degree `≥ 2`), `[a, b]` is a rational interval isolating `α` among the real roots,
and `e` encodes `ε > 0`. -/
def ValidRothInput (inp : List ℤ × (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ)) (α : ℝ) : Prop :=
  let f := polyOfList inp.1
  let a := inp.2.1; let b := inp.2.2.1; let e := inp.2.2.2
  f.IsPrimitive ∧ Irreducible f ∧ 0 < f.leadingCoeff ∧ 2 ≤ f.natDegree ∧
  0 < a.2 ∧ 0 < b.2 ∧ 0 < e.2 ∧ 0 < ratOfPair e ∧
  aeval α f = 0 ∧ (ratOfPair a : ℝ) ≤ α ∧ α ≤ ratOfPair b ∧
  ∀ β : ℝ, (ratOfPair a : ℝ) ≤ β → β ≤ ratOfPair b → aeval β f = 0 → β = α

/-- **ProofAtlas 194 (OPEN): effective Roth theorem.**

ProofAtlas `exactTarget` (quoted): "There exists one total computable algorithm which, given a
real algebraic irrational alpha by its integer minimal polynomial and a rational isolating
interval, and a positive rational epsilon, returns an integer Q>=1 such that every reduced
rational p/q, with p an integer and q>=1 an integer, satisfying |alpha-p/q|<q^(-2-epsilon) has
q<=Q. The algorithm must halt with this guarantee on every valid input. No time, space,
practical-size or software-implementation requirement is imposed."

Modelling choices:
* "total computable algorithm" is a function `F` with Mathlib's `Computable F` (partial
  recursive and total, w.r.t. the standard `Primcodable` encodings of `List ℤ`, `ℤ × ℕ`, `ℕ`);
* inputs are encoded as `(coefficient list, a, b, ε)` with rationals given as
  (numerator, denominator) pairs, so the encoding is the plain one, not Mathlib's
  `Denumerable ℚ`; `ValidRothInput` spells out validity (integer minimal polynomial =
  primitive, irreducible over `ℤ`, positive leading coefficient, degree `≥ 2`; closed interval
  `[a, b]` containing exactly one real root). The output on invalid inputs is unconstrained;
* "reduced" is `Int.gcd p q = 1`; `q^(-2-ε)` is a real power `rpow`.

Roth's theorem itself (the ineffective finiteness statement) is **not** in Mathlib and is not
formalised here. -/
def EffectiveRoth : Prop :=
  ∃ F : List ℤ × (ℤ × ℕ) × (ℤ × ℕ) × (ℤ × ℕ) → ℕ, Computable F ∧
    ∀ inp α, ValidRothInput inp α → 1 ≤ F inp ∧
      ∀ (p : ℤ) (q : ℕ), 1 ≤ q → Int.gcd p q = 1 →
        |α - p / q| < (q : ℝ) ^ (-(2 + (ratOfPair inp.2.2.2 : ℝ))) → q ≤ F inp

/-! ## ProofAtlas 351: Minkowski's conjecture on products of inhomogeneous linear forms -/

/-- Minkowski's assertion in dimension `n`: for every real `n × n` matrix `A` with
`|det A| = 1` and every `x ∈ ℝⁿ` there is `m ∈ ℤⁿ` with `∏ᵢ |xᵢ + (A m)ᵢ| ≤ 2^(-n)`. -/
def MinkowskiInDim (n : ℕ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℝ, |A.det| = 1 → ∀ x : Fin n → ℝ,
    ∃ m : Fin n → ℤ, ∏ i, |x i + (A *ᵥ (fun j => (m j : ℝ))) i| ≤ (1 / 2 : ℝ) ^ n

/-- **ProofAtlas 351 (OPEN, with solved subcases): Minkowski's conjecture.**

ProofAtlas `exactTarget` (quoted): "For every dimension n>=1, every real nonsingular n by n
matrix A with |det A|=1 and every translation x in R^n, there exists an integer vector m in Z^n
such that the product over i=1,...,n of |x_i+(Am)_i| is at most 2^(-n). The quantifier requires
an ACTUAL integer witness at the closed bound, not merely an infimum no greater than the bound.
Equivalently, scaling a general real nonsingular matrix B and its translation by
|det B|^(-1/n) gives the same actual-witness assertion with bound |det B|/2^n; all coefficients
and translations are real. No equality characterization of extremal lattices, well-rounded
Euclidean covering assertion, positive-characteristic analogue or constructive algorithm is
appended. Preserve all dimensions, not merely a selected high-dimensional open remainder."

Modelling choices: matrices `Matrix (Fin n) (Fin n) ℝ`, `|det A| = 1` (which implies
nonsingular), integer witness `m : Fin n → ℤ` cast to `ℝ`, closed bound `(1/2)^n`. The
"equivalently" rescaled form for general `B` is not separately stated. The cases
`n ≤ 10` are theorems in the literature (Minkowski `n = 2`, Remak `n = 3`, Dyson `n = 4`,
Skubenko/McMullen/Hans-Gill–Raka–Sehmi up to `n = 10`); only `n = 1` is formalised here. -/
def MinkowskiConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → MinkowskiInDim n

/-- **Known result** (trivial case `n = 1` of Minkowski's conjecture; rounding): if `|a| = 1`
then every real `x` is within `1/2` of `a·ℤ`. -/
theorem minkowskiInDim_one : MinkowskiInDim 1 := by
  intro A hA x
  set a := A 0 0 with ha
  rw [Matrix.det_fin_one] at hA
  have ha2 : a * a = 1 := by
    have := abs_mul_abs_self a; rw [hA] at this; linarith
  refine ⟨fun _ => round (-(a * x 0)), ?_⟩
  simp only [Fin.prod_univ_one, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  rw [← ha]
  have : x 0 + a * (round (-(a * x 0)) : ℝ) = a * ((round (-(a * x 0)) : ℝ) - (-(a * x 0))) := by
    linear_combination (-(x 0)) * ha2
  rw [this, abs_mul, hA, one_mul, abs_sub_comm]
  simpa using abs_sub_round (-(a * x 0))

/-! ## ProofAtlas 497: Wirsing's conjecture -/

/-- Height of a polynomial over `ℤ`: maximal absolute value of its coefficients. -/
def intPolyHeight (P : ℤ[X]) : ℕ := P.support.sup fun i => (P.coeff i).natAbs

/-- `α` is a real algebraic number of degree `≤ n` whose primitive irreducible minimal
polynomial over `ℤ` has height `H`. (The primitive irreducible integer polynomial vanishing at
`α` is unique up to sign, so `H` is determined by `α`.) -/
def IsAlgDegLeHeight (n : ℕ) (α : ℝ) (H : ℕ) : Prop :=
  ∃ P : ℤ[X], P.IsPrimitive ∧ Irreducible P ∧ aeval α P = 0 ∧ P.natDegree ≤ n ∧
    H = intPolyHeight P

/-- The real algebraic `α` of degree `≤ n` with `0 < |ξ - α| ≤ H(α)^(-w-1)`. -/
def wirsingApproxSet (n : ℕ) (ξ w : ℝ) : Set ℝ :=
  {α | ∃ H : ℕ, IsAlgDegLeHeight n α H ∧ 0 < |ξ - α| ∧ |ξ - α| ≤ (H : ℝ) ^ (-w - 1)}

/-- The exponent `w_n^*(ξ)`: the supremum (in `EReal`) of the real `w` for which
`wirsingApproxSet n ξ w` is infinite. -/
noncomputable def wStar (n : ℕ) (ξ : ℝ) : EReal :=
  sSup ((fun w : ℝ => (w : EReal)) '' {w : ℝ | (wirsingApproxSet n ξ w).Infinite})

/-- **ProofAtlas 497 (OPEN, with solved subcases): Wirsing's conjecture.**

ProofAtlas `exactTarget` (quoted): "For every positive integer n and every transcendental real
number xi, w_n^*(xi)>=n. Here w_n^*(xi) is the supremum of real w such that
0<|xi-alpha|<=H(alpha)^(-w-1) for infinitely many real algebraic numbers alpha of degree at
most n, and H(alpha) is the maximum absolute coefficient of its primitive irreducible minimal
polynomial over Z. Equivalently the approximation inequality with exponent n+1-epsilon holds
for infinitely many such alpha for every epsilon>0."

Modelling choices: transcendental is `Transcendental ℚ ξ`; `w_n^*` is `wStar n ξ`, a
supremum in `EReal` (so `+∞` is allowed, and the empty set gives `⊥`); the minimal polynomial
is any primitive irreducible `P ∈ ℤ[X]` with `P(α) = 0` (`IsAlgDegLeHeight`); `H(α)^(-w-1)` is
`rpow`. The "equivalently" form is proved equivalent in `wirsingFor_iff`. -/
def WirsingConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ξ : ℝ, Transcendental ℚ ξ → (n : EReal) ≤ wStar n ξ

lemma one_le_intPolyHeight {P : ℤ[X]} (hP : P ≠ 0) : 1 ≤ intPolyHeight P := by
  obtain ⟨i, hi⟩ : ∃ i, P.coeff i ≠ 0 := by
    by_contra h; push Not at h; exact hP (Polynomial.ext (by simpa using h))
  have : (P.coeff i).natAbs ≤ intPolyHeight P :=
    Finset.le_sup (f := fun i => (P.coeff i).natAbs) (mem_support_iff.mpr hi)
  have : 0 < (P.coeff i).natAbs := Int.natAbs_pos.mpr hi
  omega

lemma wirsingApproxSet_anti (n : ℕ) (ξ : ℝ) {w w' : ℝ} (h : w' ≤ w) :
    wirsingApproxSet n ξ w ⊆ wirsingApproxSet n ξ w' := by
  rintro α ⟨H, ⟨P, hP1, hP2, hP3, hP4, rfl⟩, h0, hle⟩
  refine ⟨_, ⟨P, hP1, hP2, hP3, hP4, rfl⟩, h0, hle.trans ?_⟩
  have : (1 : ℝ) ≤ (intPolyHeight P : ℝ) := by exact_mod_cast one_le_intPolyHeight hP2.ne_zero
  exact Real.rpow_le_rpow_of_exponent_le this (by linarith)

/-- Bridge: `w_n^*(ξ) ≥ n` iff for every `ε > 0` infinitely many real algebraic `α` of degree
`≤ n` satisfy `0 < |ξ - α| ≤ H(α)^(-(n+1-ε))` (the "equivalently" clause of the target). -/
theorem wirsingFor_iff (n : ℕ) (ξ : ℝ) :
    (n : EReal) ≤ wStar n ξ ↔ ∀ ε : ℝ, 0 < ε → (wirsingApproxSet n ξ (n - ε)).Infinite := by
  constructor
  · intro h ε hε
    have hlt : ((n - ε : ℝ) : EReal) < wStar n ξ :=
      lt_of_lt_of_le (by exact_mod_cast (by linarith : (n : ℝ) - ε < n)) h
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt'⟩ := lt_sSup_iff.mp hlt
    exact hw.mono (wirsingApproxSet_anti n ξ (EReal.coe_lt_coe_iff.mp hlt').le)
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨z, hz1, hz2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
    have hz : z < (n : ℝ) := by exact_mod_cast hz2
    have hmem : (wirsingApproxSet n ξ z).Infinite := by
      have := h (n - z) (by linarith)
      simpa using this
    have : (z : EReal) ≤ wStar n ξ := le_sSup ⟨z, hmem, rfl⟩
    exact absurd hz1 (not_lt.mpr this)

lemma rat_isAlgDegLeHeight (q : ℚ) :
    IsAlgDegLeHeight 1 (q : ℝ) (intPolyHeight (C (q.den : ℤ) * X + C (-q.num))) ∧
      intPolyHeight (C (q.den : ℤ) * X + C (-q.num)) ≤ max q.num.natAbs q.den := by
  set P : ℤ[X] := C (q.den : ℤ) * X + C (-q.num) with hP
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdeg : P.degree = 1 := degree_linear hd
  have hnat : P.natDegree = 1 := natDegree_eq_of_degree_eq_some hdeg
  have hirr : Irreducible P := by
    apply irreducible_of_degree_eq_one_of_isRelPrime_coeff hdeg
    have h0 : P.coeff 0 = -q.num := by simp only [hP, coeff_add, coeff_C_mul, coeff_X, coeff_C]; simp
    have h1 : P.coeff 1 = q.den := by simp only [hP, coeff_add, coeff_C_mul, coeff_X, coeff_C]; simp
    rw [h0, h1]
    exact (Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd, Int.natAbs_neg] using q.reduced)).isRelPrime
  refine ⟨⟨P, hirr.isPrimitive (by omega), hirr, ?_, hnat.le, rfl⟩, ?_⟩
  · rw [hP, map_add, map_mul, aeval_C, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast, eq_intCast]
    push_cast
    have : (q : ℝ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    rw [this]; field_simp; ring
  · unfold intPolyHeight
    apply Finset.sup_le
    intro i _
    rcases i with _ | _ | i <;> simp only [hP, coeff_add, coeff_C_mul, coeff_X, coeff_C] <;> simp

lemma finite_rat_abs_le_den_lt (c : ℝ) (D : ℕ) :
    {q : ℚ | |(q : ℝ)| ≤ c ∧ q.den < D}.Finite := by
  set K : ℤ := ⌈c * D⌉
  refine ((((Finset.range D) ×ˢ (Finset.Icc (-K) K)).image
    (fun p : ℕ × ℤ => (p.2 : ℚ) / p.1)).finite_toSet).subset ?_
  rintro q ⟨hq, hd⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
    Finset.mem_range, Finset.mem_Icc, Prod.exists]
  refine ⟨q.den, q.num, ⟨hd, ?_⟩, Rat.num_div_den q⟩
  have hnum : ((q.num : ℝ)) = (q : ℝ) * q.den := by
    have := Rat.mul_den_eq_num q
    exact_mod_cast this.symm
  have hle : |(q.num : ℝ)| ≤ c * D := by
    rw [hnum, abs_mul, Nat.abs_cast]
    have : (q.den : ℝ) ≤ D := by exact_mod_cast hd.le
    have hc : 0 ≤ c := (abs_nonneg _).trans hq
    calc |(q : ℝ)| * q.den ≤ c * q.den := by gcongr
      _ ≤ c * D := by gcongr
  have hK : c * D ≤ (K : ℝ) := Int.le_ceil _
  have h2 := abs_le.mp (hle.trans hK)
  constructor
  · have : ((-K : ℤ) : ℝ) ≤ q.num := by push_cast; linarith
    exact_mod_cast this
  · exact_mod_cast h2.2

/-- **Known result** (the case `n = 1` of Wirsing's conjecture, a consequence of Dirichlet's
approximation theorem; see Y. Bugeaud, *Approximation by algebraic numbers*, Cambridge 2004,
§3.1): for every irrational real `ξ` (in particular every transcendental one),
`w_1^*(ξ) ≥ 1`. Proof: the infinitely many `p/q` with `|ξ - p/q| < 1/q²` have height
`H(p/q) = max(|p|, q) ≤ (|ξ|+1) q`, hence satisfy `|ξ - p/q| ≤ H^(-(2-ε))` once `q` is large. -/
theorem wirsing_one {ξ : ℝ} (hξ : Irrational ξ) : ((1 : ℕ) : EReal) ≤ wStar 1 ξ := by
  rw [wirsingFor_iff]
  intro ε hε
  set e := min ε (1 / 2) with he
  have he0 : 0 < e := lt_min hε (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  refine Set.Infinite.mono (wirsingApproxSet_anti 1 ξ (show ((1 : ℕ) : ℝ) - ε ≤ 1 - e by
    push_cast; linarith [min_le_left ε (1 / 2)])) ?_
  set c := |ξ| + 1 with hc
  have hc1 : 1 ≤ c := by have := abs_nonneg ξ; linarith
  -- choose `D` with `c² ≤ D^e`
  set D : ℕ := ⌈c ^ (2 / e)⌉₊ with hD
  have hD : c ^ (2 : ℝ) ≤ (D : ℝ) ^ e := by
    have h1 : c ^ (2 / e) ≤ (D : ℝ) := Nat.le_ceil _
    have h2 := Real.rpow_le_rpow (by positivity) h1 he0.le
    rwa [← Real.rpow_mul (by linarith), div_mul_cancel₀ _ he0.ne'] at h2
  set S := {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}
  have hS : (S \ {q : ℚ | |(q : ℝ)| ≤ c ∧ q.den < D}).Infinite :=
    (Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ).sdiff
      (finite_rat_abs_le_den_lt c D)
  refine Set.Infinite.mono ?_ (hS.image (Rat.cast_injective (α := ℝ)).injOn)
  rintro _ ⟨q, ⟨hqS, hqF⟩, rfl⟩
  have hqS' : |ξ - q| < 1 / (q.den : ℝ) ^ 2 := hqS
  have hden1 : (1 : ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hsmall : 1 / (q.den : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hqc : |(q : ℝ)| ≤ c := by
    have := abs_sub_abs_le_abs_sub (q : ℝ) ξ
    rw [abs_sub_comm] at this
    linarith
  have hqD : D ≤ q.den := by
    by_contra h; exact hqF ⟨hqc, by omega⟩
  obtain ⟨hAlg, hHle⟩ := rat_isAlgDegLeHeight q
  refine ⟨_, hAlg, abs_pos.mpr (sub_ne_zero.mpr (hξ.ne_rat q)), le_of_lt (hqS'.trans_le ?_)⟩
  set H := intPolyHeight (C (q.den : ℤ) * X + C (-q.num))
  have hH1 : (1 : ℝ) ≤ H := by
    obtain ⟨P, -, hP, -, -, hPH⟩ := hAlg
    rw [hPH]; exact_mod_cast one_le_intPolyHeight hP.ne_zero
  have hnum : |(q.num : ℝ)| = |(q : ℝ)| * q.den := by
    have := Rat.mul_den_eq_num q
    rw [show ((q.num : ℝ)) = (q : ℝ) * q.den by exact_mod_cast this.symm, abs_mul, Nat.abs_cast]
  have hHc : (H : ℝ) ≤ c * q.den := by
    have h1 : (H : ℝ) ≤ max (q.num.natAbs : ℝ) q.den := by exact_mod_cast hHle
    have h2 : (q.num.natAbs : ℝ) ≤ c * q.den := by
      rw [Nat.cast_natAbs, Int.cast_abs, hnum]; gcongr
    have h3 : (q.den : ℝ) ≤ c * q.den := by nlinarith
    exact h1.trans (max_le h2 h3)
  -- the exponent
  have hexp : -(1 - e) - 1 = -(2 - e) := by ring
  rw [hexp]
  have hstep1 : (c * q.den) ^ (-(2 - e)) ≤ (H : ℝ) ^ (-(2 - e)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hHc (by linarith)
  refine le_trans ?_ hstep1
  rw [Real.mul_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith),
    Real.rpow_neg (by linarith)]
  -- `1/den² ≤ c^-(2-e) · den^-(2-e)`
  have hce : c ^ (2 - e) ≤ (q.den : ℝ) ^ e := by
    calc c ^ (2 - e) ≤ c ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by linarith)
      _ ≤ (D : ℝ) ^ e := hD
      _ ≤ (q.den : ℝ) ^ e := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqD) he0.le
  have hdpos : (0 : ℝ) < q.den := by linarith
  have hsplit : (q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 - e) * (q.den : ℝ) ^ e := by
    rw [← Real.rpow_add hdpos]; norm_num
  have hpos1 : 0 < c ^ (2 - e) := by positivity
  have hpos2 : 0 < (q.den : ℝ) ^ (2 - e) := by positivity
  rw [show ((q.den : ℝ)) ^ 2 = (q.den : ℝ) ^ (2 : ℝ) by norm_cast, hsplit, ← mul_inv,
    one_div]
  apply inv_anti₀ (by positivity)
  rw [mul_comm]
  gcongr

/-- `WirsingConjecture` restricted to `n = 1` holds (**Known result**, `wirsing_one`): this is
only the solved subcase `n = 1`, not progress on general `n`. -/
theorem wirsingConjecture_one :
    ∀ ξ : ℝ, Transcendental ℚ ξ → ((1 : ℕ) : EReal) ≤ wStar 1 ξ := by
  intro ξ hξ
  refine wirsing_one ?_
  rintro ⟨q, rfl⟩
  exact hξ (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) q)

end CryptoLean.OpenProblems.NumberTheory.Approximation

#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.digit_eq_real_digits_fract
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.rat_not_isNormalInBase
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.rat_not_isNormalInBase_ten
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.borel_irrational_hyp_needed
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.dirichlet_approximation
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.dirichlet_infinitely_many
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.liouville_inequality
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.minkowskiInDim_one
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.wirsingFor_iff
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.wirsing_one
#print axioms CryptoLean.OpenProblems.NumberTheory.Approximation.wirsingConjecture_one
