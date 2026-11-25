import Mathlib

/-!
# Linear-programming open problems: #136 (polynomial simplex pivot rule) and
# #169 (integrality gap of the subtour LP for metric TSP)

Both problems are **open**. Each appears below only as an unproved `def … : Prop`; nothing in
this file resolves, or suggests a resolution of, either problem. The proved theorems are
classical known results, used to check that the definitions mean what they should.

## Problem #136 (ProofAtlas, edition 2026-11-12)

Linear programs are in standard form `min cᵀx` subject to `A x = b`, `x ≥ 0` over `ℚ`
(`LP`). A basis is a set of `m` linearly independent columns; its basic solution is the
solution of `A x = b` supported on the basis. A pivot rule is modelled abstractly
(`PivotRule`): given the LP and the history of visited bases it returns a probability
distribution (`PMF`) on next bases; a deterministic rule returns a point mass. Its run is the
Markov chain `histDist`, and the expected number of pivots is the tail sum `expectedPivots`.

* Open problem #136 is recorded only as the `Prop` `PolynomialPivotRule` (unproved), with
  `PolynomialPivotRuleProblem` its instance for unrestricted rules.
* Proved (known results): LP weak duality (`weak_duality`), the optimality certificate given
  by equal objective values (`optimal_of_eq`, `dual_optimal_of_eq`), and the sanity fact that a
  run started at an optimal basis makes no pivot (`expectedPivots_eq_zero_of_optimal`).

## Problem #169 (ProofAtlas, edition 2026-11-12)

A metric TSP instance is a metric `d` on `Fin n` (`IsMetric`); a tour is a cyclic permutation
`σ` of all of `Fin n` (`IsTour`, the successor map of a Hamiltonian cycle) of cost
`∑ᵢ d(i, σ i)`. The subtour (Held–Karp) LP is `SubtourFeasible`; `optValue` and `lpValue` are
the integral and LP optima, and `gapSet` is the set of ratios `OPT/LP` over all metric instances
with `n ≥ 3`. The integrality gap is the supremum of `gapSet`.

* Open problem #169 is recorded only as the `Prop` `SubtourGapEqFourThirds` (unproved).
* Proved (known results): the incidence vector of every tour is feasible for the subtour LP and
  has the tour's cost (`tourVec_feasible`, `lpCost_tourVec`), hence `LP ≤ OPT`
  (`lpValue_le_optValue`) and every ratio in `gapSet` is at least `1` (`one_le_of_mem_gapSet`);
  and an explicit 6-vertex metric (the triangular prism with triangle edges of length 2 and
  rungs of length 1) has `LP ≤ 9 < 10 ≤ OPT`, so `gapSet` contains a ratio `≥ 10/9`
  (`exists_mem_gapSet_ge_ten_ninths`). Only the ratio `10/9` is certified here.
-/

namespace CryptoLean.OpenProblems.LinearProgramming

open Finset Matrix

/-! ## Part 1: linear programs in standard form and the pivot-rule model (#136) -/

/-- A linear program in standard form with `m` equality constraints and `n` variables over `ℚ`:
minimize `c ⬝ᵥ x` subject to `A *ᵥ x = b`, `x ≥ 0`. -/
structure LP (m n : ℕ) where
  /-- constraint matrix -/
  A : Matrix (Fin m) (Fin n) ℚ
  /-- right-hand side -/
  b : Fin m → ℚ
  /-- objective -/
  c : Fin n → ℚ

variable {m n : ℕ}

/-- Primal feasibility: `A x = b` and `x ≥ 0`. -/
def LP.Feasible (P : LP m n) (x : Fin n → ℚ) : Prop := P.A *ᵥ x = P.b ∧ 0 ≤ x

/-- Dual feasibility for the standard-form dual `max bᵀy` s.t. `Aᵀ y ≤ c`. -/
def LP.DualFeasible (P : LP m n) (y : Fin m → ℚ) : Prop := y ᵥ* P.A ≤ P.c

/-- The LP is bounded: its objective is bounded below on the feasible region. -/
def LP.BoundedBelow (P : LP m n) : Prop := ∃ L : ℚ, ∀ x, P.Feasible x → L ≤ P.c ⬝ᵥ x

/-- `B` is a basis: `m` columns of `A` that are linearly independent. -/
def LP.IsBasis (P : LP m n) (B : Finset (Fin n)) : Prop :=
  B.card = m ∧ LinearIndependent ℚ (fun j : B => fun i => P.A i j)

/-- `x` is the basic solution of `B`: it solves `A x = b` and vanishes off `B` (for a basis it is
unique). -/
def LP.IsBasicSolution (P : LP m n) (B : Finset (Fin n)) (x : Fin n → ℚ) : Prop :=
  P.A *ᵥ x = P.b ∧ ∀ j ∉ B, x j = 0

/-- `B` is a feasible basis: a basis whose basic solution is nonnegative. -/
def LP.IsFeasibleBasis (P : LP m n) (B : Finset (Fin n)) : Prop :=
  P.IsBasis B ∧ ∃ x, P.IsBasicSolution B x ∧ 0 ≤ x

/-- Nondegeneracy: every basic feasible solution has all its basic variables strictly
positive. -/
def LP.Nondegenerate (P : LP m n) : Prop :=
  ∀ B x, P.IsBasis B → P.IsBasicSolution B x → 0 ≤ x → ∀ j ∈ B, 0 < x j

/-- `B` is an optimal basis: a feasible basis whose basic solution minimizes the objective over
the whole feasible region. -/
def LP.IsOptimalBasis (P : LP m n) (B : Finset (Fin n)) : Prop :=
  P.IsFeasibleBasis B ∧ ∀ x, P.IsBasicSolution B x → ∀ y, P.Feasible y → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ y

/-- Two bases are adjacent when one is obtained from the other by swapping one column. -/
def Adjacent (B B' : Finset (Fin n)) : Prop := (B \ B').card = 1 ∧ (B' \ B).card = 1

/-- A simplex pivot from `B` to `B'`: `B'` is an adjacent feasible basis with strictly smaller
objective value. (For a nondegenerate LP this is exactly a pivot on an entering column of
negative reduced cost with the ratio-test leaving column.) -/
def LP.IsPivot (P : LP m n) (B B' : Finset (Fin n)) : Prop :=
  Adjacent B B' ∧ P.IsFeasibleBasis B' ∧
    ∀ x x', P.IsBasicSolution B x → P.IsBasicSolution B' x' → P.c ⬝ᵥ x' < P.c ⬝ᵥ x

/-- An abstract (possibly randomized, possibly history-dependent) pivot rule: given an LP and
the history of visited bases (most recent first), a distribution on the next basis.
A deterministic rule is one whose outputs are point masses `PMF.pure`. -/
structure PivotRule where
  /-- the distribution of the next basis given the LP and the history -/
  next : ∀ {m n : ℕ}, LP m n → List (Finset (Fin n)) → PMF (Finset (Fin n))

/-- A rule is a simplex pivot rule if, on every bounded nondegenerate LP, from a feasible
non-optimal current basis it only ever moves to a simplex pivot. -/
def PivotRule.Valid (R : PivotRule) : Prop :=
  ∀ {m n : ℕ} (P : LP m n), P.BoundedBelow → P.Nondegenerate →
    ∀ (B : Finset (Fin n)) (t : List (Finset (Fin n))), P.IsFeasibleBasis B →
      ¬ P.IsOptimalBasis B → ∀ B' ∈ (R.next P (B :: t)).support, P.IsPivot B B'

open Classical in
/-- One step of a run: stop (stay put) at an optimal basis, otherwise pivot by the rule. -/
noncomputable def step (R : PivotRule) (P : LP m n) :
    List (Finset (Fin n)) → PMF (List (Finset (Fin n)))
  | [] => PMF.pure []
  | B :: t => if P.IsOptimalBasis B then PMF.pure (B :: t)
      else (R.next P (B :: t)).map (· :: B :: t)

/-- Distribution of the history after `k` steps of the run started at `B₀`. -/
noncomputable def histDist (R : PivotRule) (P : LP m n) (B₀ : Finset (Fin n)) :
    ℕ → PMF (List (Finset (Fin n)))
  | 0 => PMF.pure [B₀]
  | k + 1 => (histDist R P B₀ k).bind (step R P)

/-- Histories whose current basis is not optimal. -/
def notOptimal (P : LP m n) : Set (List (Finset (Fin n))) :=
  {h | ∃ B, h.head? = some B ∧ ¬ P.IsOptimalBasis B}

/-- Expected number of pivots until an optimal basis is reached:
`E[T] = ∑ₖ Pr[T > k]`, with `T > k` iff the basis after `k` steps is not optimal. For a
deterministic rule this is the number of pivots (possibly `∞`). -/
noncomputable def expectedPivots (R : PivotRule) (P : LP m n) (B₀ : Finset (Fin n)) : ENNReal :=
  ∑' k, (histDist R P B₀ k).toOuterMeasure (notOptimal P)

/-- **Open problem #136** (ProofAtlas, edition 2026-11-12), relative to a class `Admissible` of
pivot rules. Exact statement:

> "Construct a deterministic or randomized simplex pivot rule and a polynomial p such that,
> for every bounded nondegenerate rational linear program with m equality constraints and n
> variables and every feasible starting basis, the rule reaches an optimal basis in at most
> p(m,n) pivots, in expectation when the rule is randomized; or prove that no such rule
> exists."

The problem asks to prove this `Prop` (for the intended class of rules) or its negation; it is
**open** and is not proved here.

Modelling simplifications, stated honestly:
* LPs are in standard form over `ℚ`; "bounded" is read as "objective bounded below on the
  feasible region"; "nondegenerate" as "every basic feasible solution has all basic variables
  positive" (`LP.Nondegenerate`).
* A pivot is any move to an adjacent feasible basis with strictly smaller objective
  (`LP.IsPivot`); under nondegeneracy these are exactly the simplex pivots. A rule must make
  such moves only on bounded nondegenerate LPs from feasible non-optimal bases
  (`PivotRule.Valid`).
* Randomized rules are modelled as history-dependent transition distributions (`PMF`), which
  covers rules using fresh random bits at each step; the expectation is the tail sum of the
  induced Markov chain.
* "A polynomial p(m,n)" is replaced by the equivalent (for nonnegative monotone bounds) form
  `C · (m+n+1)^k`.
* The model places no computability or per-step-efficiency restriction on rules; that is what
  the parameter `Admissible` is for. With `Admissible = fun _ => True`
  (`PolynomialPivotRuleProblem`) even non-computable rules are allowed, which makes the
  question one about lengths of strictly monotone edge paths on polytopes (itself open). -/
def PolynomialPivotRule (Admissible : PivotRule → Prop) : Prop :=
  ∃ R : PivotRule, Admissible R ∧ R.Valid ∧ ∃ C k : ℕ,
    ∀ (m n : ℕ) (P : LP m n), P.BoundedBelow → P.Nondegenerate →
      ∀ B₀, P.IsFeasibleBasis B₀ → expectedPivots R P B₀ ≤ ((C * (m + n + 1) ^ k : ℕ) : ENNReal)

/-- Open problem #136 for unrestricted rules (see `PolynomialPivotRule`). Unproved and open. -/
def PolynomialPivotRuleProblem : Prop := PolynomialPivotRule fun _ => True

/-- **Known result** (LP weak duality; e.g. Schrijver, *Theory of Linear and Integer
Programming*, 1986, §7.4; Chvátal, *Linear Programming*, 1983, Ch. 5): for a primal feasible `x`
and a dual feasible `y` of a standard-form LP, `bᵀy ≤ cᵀx`. -/
theorem weak_duality (P : LP m n) {x : Fin n → ℚ} {y : Fin m → ℚ} (hx : P.Feasible x)
    (hy : P.DualFeasible y) : P.b ⬝ᵥ y ≤ P.c ⬝ᵥ x := by
  obtain ⟨hAx, hx0⟩ := hx
  rw [← hAx, dotProduct_comm, dotProduct_mulVec, dotProduct_comm (y ᵥ* P.A),
    dotProduct_comm P.c]
  unfold dotProduct
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hy i) (hx0 i)

/-- **Known result** (optimality certificate, a corollary of weak duality; Schrijver 1986,
§7.4): if a primal feasible `x` and a dual feasible `y` have equal objective values then `x` is
primal optimal. -/
theorem optimal_of_eq (P : LP m n) {x : Fin n → ℚ} {y : Fin m → ℚ} (_hx : P.Feasible x)
    (hy : P.DualFeasible y) (h : P.c ⬝ᵥ x = P.b ⬝ᵥ y) :
    ∀ x', P.Feasible x' → P.c ⬝ᵥ x ≤ P.c ⬝ᵥ x' := fun x' hx' => by
  rw [h]; exact weak_duality P hx' hy

/-- **Known result** (dual half of the optimality certificate; Schrijver 1986, §7.4). -/
theorem dual_optimal_of_eq (P : LP m n) {x : Fin n → ℚ} {y : Fin m → ℚ} (hx : P.Feasible x)
    (_hy : P.DualFeasible y) (h : P.c ⬝ᵥ x = P.b ⬝ᵥ y) :
    ∀ y', P.DualFeasible y' → P.b ⬝ᵥ y' ≤ P.b ⬝ᵥ y := fun y' hy' => by
  rw [← h]; exact weak_duality P hx hy'

/-- Sanity check of the run model: from an optimal basis the run never moves. -/
theorem histDist_of_optimal (R : PivotRule) (P : LP m n) {B₀ : Finset (Fin n)}
    (hB : P.IsOptimalBasis B₀) (k : ℕ) : histDist R P B₀ k = PMF.pure [B₀] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [histDist, ih, PMF.pure_bind]
    simp [step, hB]

/-- Sanity check of the run model: started at an optimal basis, the expected number of pivots
is `0`. -/
theorem expectedPivots_eq_zero_of_optimal (R : PivotRule) (P : LP m n) {B₀ : Finset (Fin n)}
    (hB : P.IsOptimalBasis B₀) : expectedPivots R P B₀ = 0 := by
  unfold expectedPivots
  simp only [histDist_of_optimal R P hB, PMF.toOuterMeasure_pure_apply]
  simp [notOptimal, hB]

/-! ## Part 2: metric TSP and the subtour LP (#169) -/

/-- A (pseudo)metric on `Fin n`. -/
structure IsMetric {n : ℕ} (d : Fin n → Fin n → ℝ) : Prop where
  self : ∀ i, d i i = 0
  symm : ∀ i j, d i j = d j i
  nonneg : ∀ i j, 0 ≤ d i j
  triangle : ∀ i j k, d i k ≤ d i j + d j k

/-- A tour (Hamiltonian cycle) given by its successor map: a single cycle through every
vertex. -/
def IsTour {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop := σ.IsCycle ∧ σ.support = univ

/-- Cost of a tour. -/
def tourCost {n : ℕ} (d : Fin n → Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ := ∑ i, d i (σ i)

/-- Cost of an edge vector `x` stored symmetrically (`x i j = x j i` is the value on edge
`{i,j}`): `∑_{i<j} d i j x i j = ½ ∑_{i,j} d i j x i j`. -/
noncomputable def lpCost {n : ℕ} (d : Fin n → Fin n → ℝ) (x : Fin n → Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j, d i j * x i j

/-- Feasibility for the subtour (Held–Karp) LP: `0 ≤ x_e ≤ 1`, degree `2` at every vertex,
and `x(δ(S)) ≥ 2` for every proper nonempty `S`. -/
def SubtourFeasible {n : ℕ} (x : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, x i j = x j i) ∧ (∀ i, x i i = 0) ∧ (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧
    (∀ i, ∑ j, x i j = 2) ∧
    ∀ S : Finset (Fin n), S.Nonempty → S ≠ univ → 2 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, x i j

/-- Optimal tour cost. -/
noncomputable def optValue {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  sInf (tourCost d '' {σ | IsTour σ})

/-- Optimal value of the subtour LP. -/
noncomputable def lpValue {n : ℕ} (d : Fin n → Fin n → ℝ) : ℝ :=
  sInf (lpCost d '' {x | SubtourFeasible x})

/-- The ratios `OPT/LP` over all metric instances on `n ≥ 3` vertices with positive LP value.
The integrality gap of the subtour LP is the supremum of this set. -/
def gapSet : Set ℝ :=
  {r | ∃ (n : ℕ) (d : Fin n → Fin n → ℝ), 3 ≤ n ∧ IsMetric d ∧ 0 < lpValue d ∧
    r = optValue d / lpValue d}

/-- **Open problem #169** (ProofAtlas, edition 2026-11-12). Exact statement:

> "Prove or disprove that the integrality gap of the subtour (Held-Karp) LP relaxation of the
> symmetric metric traveling salesman problem equals 4/3."

Stated as: `4/3` is the least upper bound of the set `gapSet` of ratios `OPT/LP`. The problem
asks to prove this `Prop` or its negation; it is **open** and is not proved here.

Modelling simplifications, stated honestly:
* Instances are metrics on `Fin n` with `n ≥ 3`, real-valued, and pseudometrics (distinct
  points at distance `0`) are allowed.
* Instances with LP value `0` are excluded from `gapSet` to avoid `0/0`.
* Edge variables are stored as a symmetric matrix with zero diagonal; the LP value is the
  infimum (`sInf`) of the cost over the feasible region (it is attained, but that is not used).
* Tours are successor maps of Hamiltonian cycles (`IsTour`); both orientations of a cycle are
  separate permutations of the same cost, which does not affect `optValue`. -/
def SubtourGapEqFourThirds : Prop := IsLUB gapSet (4 / 3)

/-! ### Tours -/

section Tours

variable {n : ℕ} {σ : Equiv.Perm (Fin n)}

theorem IsTour.apply_ne (hσ : IsTour σ) (i : Fin n) : σ i ≠ i := by
  rw [← Equiv.Perm.mem_support, hσ.2]; exact mem_univ i

theorem IsTour.inv (hσ : IsTour σ) : IsTour σ⁻¹ :=
  ⟨hσ.1.inv, by rw [Equiv.Perm.support_inv, hσ.2]⟩

/-- A nonempty vertex set mapped into itself by a tour is everything. -/
theorem IsTour.eq_univ (hσ : IsTour σ) {S : Finset (Fin n)} (hne : S.Nonempty)
    (hS : ∀ i ∈ S, σ i ∈ S) : S = univ := by
  obtain ⟨a, ha⟩ := hne
  have hpow : ∀ k : ℕ, (σ ^ k) a ∈ S := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hS _ ih
  refine eq_univ_of_forall fun b => ?_
  obtain ⟨k, hk⟩ := (hσ.1.sameCycle (hσ.apply_ne a) (hσ.apply_ne b)).exists_nat_pow_eq
  rw [← hk]; exact hpow k

/-- A tour on `n ≥ 3` vertices has no 2-cycles. -/
theorem IsTour.apply_apply_ne (hσ : IsTour σ) (hn : 3 ≤ n) (i : Fin n) : σ (σ i) ≠ i := by
  intro h
  have hS := hσ.eq_univ (S := {i, σ i}) ⟨i, by simp⟩ (by
    intro j hj
    rcases mem_insert.1 hj with rfl | hj
    · simp
    · rw [mem_singleton.1 hj, h]; simp)
  have : (univ : Finset (Fin n)).card ≤ 2 := hS ▸ card_le_two
  simp at this; omega

theorem IsTour.apply_ne_inv_apply (hσ : IsTour σ) (hn : 3 ≤ n) (i : Fin n) : σ i ≠ σ⁻¹ i := by
  intro h
  apply hσ.apply_apply_ne hn i
  rw [h]; simp

/-- The edge-incidence vector of a tour. -/
def tourVec (σ : Equiv.Perm (Fin n)) (i j : Fin n) : ℝ := if σ i = j ∨ σ j = i then 1 else 0

theorem tourVec_eq (hσ : IsTour σ) (hn : 3 ≤ n) (i j : Fin n) :
    tourVec σ i j = (if j = σ i then 1 else 0) + (if j = σ⁻¹ i then 1 else 0) := by
  have hne := hσ.apply_ne_inv_apply hn i
  have hiff : σ j = i ↔ j = σ⁻¹ i := by rw [Equiv.Perm.eq_inv_iff_eq]
  unfold tourVec
  by_cases h1 : j = σ i
  · subst h1
    simpa using hne
  · by_cases h2 : j = σ⁻¹ i
    · subst h2
      simp only [h1, ite_false]; norm_num
    · have hc : ¬ (σ i = j ∨ σ j = i) := by
        rintro (h | h); exacts [h1 h.symm, h2 (hiff.1 h)]
      simp only [hc, h1, h2, ite_false]; norm_num

/-- **Known result** (folklore; e.g. Applegate–Bixby–Chvátal–Cook, *The Traveling Salesman
Problem: A Computational Study*, 2006, §5.1): the incidence vector of every Hamiltonian cycle is
feasible for the subtour LP. -/
theorem tourVec_feasible (hσ : IsTour σ) (hn : 3 ≤ n) : SubtourFeasible (tourVec σ) := by
  refine ⟨fun i j => ?_, fun i => ?_, fun i j => ?_, fun i => ?_, fun S hne hS => ?_⟩
  · unfold tourVec
    have : (σ i = j ∨ σ j = i) ↔ (σ j = i ∨ σ i = j) := or_comm
    simp only [this]
  · have := hσ.apply_ne i; simp [tourVec, this]
  · unfold tourVec; split_ifs <;> norm_num
  · simp only [tourVec_eq hσ hn, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]; norm_num
  · -- the cut is crossed forwards and backwards
    have hc : ∀ τ : Equiv.Perm (Fin n), IsTour τ → ∃ i ∈ S, τ i ∉ S := by
      intro τ hτ; by_contra h; push Not at h; exact hS (hτ.eq_univ hne h)
    obtain ⟨i, hi, hiS⟩ := hc σ hσ
    obtain ⟨k, hk, hkS⟩ := hc σ⁻¹ hσ.inv
    rw [← sum_product' (f := fun a b => tourVec σ a b)]
    have hmem1 : (i, σ i) ∈ S ×ˢ Sᶜ := mem_product.2 ⟨hi, mem_compl.2 hiS⟩
    have hmem2 : (k, σ⁻¹ k) ∈ S ×ˢ Sᶜ := mem_product.2 ⟨hk, mem_compl.2 hkS⟩
    have hne' : (i, σ i) ≠ (k, σ⁻¹ k) := by
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      exact hσ.apply_ne_inv_apply hn i h2
    have h1 : tourVec σ i (σ i) = 1 := by simp [tourVec]
    have h2 : tourVec σ k (σ⁻¹ k) = 1 := by simp [tourVec]
    have hnn : ∀ p ∈ S ×ˢ Sᶜ, 0 ≤ tourVec σ p.1 p.2 := fun p _ => by
      unfold tourVec; split_ifs <;> norm_num
    have := add_le_sum (f := fun p : Fin n × Fin n => tourVec σ p.1 p.2) hnn hmem1 hmem2 hne'
    simp only [h1, h2] at this
    linarith

/-- **Known result** (same source): the subtour-LP cost of a tour's incidence vector is the
tour's cost. -/
theorem lpCost_tourVec {d : Fin n → Fin n → ℝ} (hd : IsMetric d) (hσ : IsTour σ) (hn : 3 ≤ n) :
    lpCost d (tourVec σ) = tourCost d σ := by
  unfold lpCost tourCost
  simp only [tourVec_eq hσ hn, mul_add, mul_ite, mul_one, mul_zero, sum_add_distrib,
    sum_ite_eq', mem_univ, ite_true]
  have : ∑ i, d i (σ⁻¹ i) = ∑ i, d i (σ i) := by
    rw [← Equiv.sum_comp σ (fun i => d i (σ⁻¹ i))]
    simp [hd.symm]
  rw [this]; ring

theorem exists_tour (hn : 3 ≤ n) : ∃ σ : Equiv.Perm (Fin n), IsTour σ :=
  ⟨finRotate n, isCycle_finRotate_of_le (by omega), support_finRotate_of_le (by omega)⟩

theorem lpCost_nonneg {d : Fin n → Fin n → ℝ} (hd : IsMetric d) {x : Fin n → Fin n → ℝ}
    (hx : SubtourFeasible x) : 0 ≤ lpCost d x := by
  unfold lpCost
  exact mul_nonneg (by norm_num) (sum_nonneg fun i _ => sum_nonneg fun j _ =>
    mul_nonneg (hd.nonneg i j) (hx.2.2.1 i j).1)

/-- **Known result** (the subtour LP is a relaxation; Held–Karp 1970, Applegate et al. 2006):
`LP ≤ OPT`. -/
theorem lpValue_le_optValue {d : Fin n → Fin n → ℝ} (hd : IsMetric d) (hn : 3 ≤ n) :
    lpValue d ≤ optValue d := by
  obtain ⟨σ₀, hσ₀⟩ := exists_tour hn
  refine le_csInf ⟨_, σ₀, hσ₀, rfl⟩ ?_
  rintro _ ⟨σ, hσ, rfl⟩
  rw [← lpCost_tourVec hd hσ hn]
  exact csInf_le ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact lpCost_nonneg hd hx⟩
    ⟨_, tourVec_feasible hσ hn, rfl⟩

/-- **Known result**: the integrality gap of the subtour LP is at least `1`; every ratio in
`gapSet` is `≥ 1`. -/
theorem one_le_of_mem_gapSet {r : ℝ} (hr : r ∈ gapSet) : 1 ≤ r := by
  obtain ⟨n, d, hn, hd, hpos, rfl⟩ := hr
  rw [le_div_iff₀ hpos, one_mul]
  exact lpValue_le_optValue hd hn

end Tours

/-! ### A 6-vertex instance with gap at least `10/9` -/

/-- Distances (as naturals) on the triangular prism: vertices `0,1,2` and `3,4,5` are the two
triangles, `i` and `i+3` are joined by a rung. Triangle edges have length `2`, rungs length `1`,
and the remaining pairs their shortest-path distance `3`. -/
def prismD (i j : Fin 6) : ℕ :=
  if i = j then 0 else if j.val = (i.val + 3) % 6 then 1
  else if (i.val < 3 ↔ j.val < 3) then 2 else 3

/-- Twice the fractional point: `1/2` on triangle edges, `1` on rungs. -/
def prismX (i j : Fin 6) : ℕ :=
  if i = j then 0 else if j.val = (i.val + 3) % 6 then 2
  else if (i.val < 3 ↔ j.val < 3) then 1 else 0

/-- The prism metric. -/
def prismMetric (i j : Fin 6) : ℝ := prismD i j

/-- The fractional subtour point on the prism. -/
noncomputable def prismFrac (i j : Fin 6) : ℝ := (prismX i j : ℝ) / 2

theorem prismMetric_isMetric : IsMetric prismMetric where
  self i := by simp [prismMetric, prismD]
  symm i j := by
    unfold prismMetric; congr 1; revert i j; decide
  nonneg i j := by unfold prismMetric; positivity
  triangle i j k := by
    unfold prismMetric; exact_mod_cast (by revert i j k; decide :
      ∀ i j k : Fin 6, prismD i k ≤ prismD i j + prismD j k) i j k

theorem prismFrac_feasible : SubtourFeasible prismFrac := by
  refine ⟨fun i j => ?_, fun i => ?_, fun i j => ?_, fun i => ?_, fun S hne hS => ?_⟩
  · unfold prismFrac; congr 2; revert i j; decide
  · simp [prismFrac, prismX]
  · unfold prismFrac
    have : prismX i j ≤ 2 := by revert i j; decide
    constructor
    · positivity
    · rw [div_le_one (by norm_num)]; exact_mod_cast this
  · unfold prismFrac
    rw [← sum_div, div_eq_iff (by norm_num)]
    have : ∑ j, prismX i j = 4 := by revert i; decide
    exact_mod_cast this
  · unfold prismFrac
    simp only [← sum_div]
    rw [le_div_iff₀ (by norm_num)]
    have : 4 ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, prismX i j := by
      revert S; decide
    norm_num; exact_mod_cast this

theorem lpCost_prismFrac : lpCost prismMetric prismFrac = 9 := by
  unfold lpCost prismMetric prismFrac
  have : ∑ i, ∑ j, prismD i j * prismX i j = 36 := by decide
  have h : ∑ i, ∑ j, (prismD i j : ℝ) * ((prismX i j : ℝ) / 2)
      = (1 / 2) * ((∑ i, ∑ j, prismD i j * prismX i j : ℕ) : ℝ) := by
    push_cast; simp only [mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  rw [h, this]; norm_num

/-- All derangements of `Fin 6` without 2-cycles cost at least `10` in the prism metric
(checked by exhaustive kernel computation). -/
theorem prism_tour_bound : ∀ a : Fin 6, a ≠ 0 → ∀ b : Fin 6, (b ≠ 1 ∧ b ≠ a) →
    ∀ c : Fin 6, (c ≠ 2 ∧ c ≠ a ∧ c ≠ b) →
    ∀ d : Fin 6, (d ≠ 3 ∧ d ≠ a ∧ d ≠ b ∧ d ≠ c) →
    ∀ e : Fin 6, (e ≠ 4 ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d) →
    ∀ f : Fin 6, (f ≠ 5 ∧ f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d ∧ f ≠ e) →
    (∀ i : Fin 6, ![a, b, c, d, e, f] (![a, b, c, d, e, f] i) ≠ i) →
    10 ≤ prismD 0 a + prismD 1 b + prismD 2 c + prismD 3 d + prismD 4 e + prismD 5 f := by
  decide

theorem prism_tourCost_ge {σ : Equiv.Perm (Fin 6)} (hσ : IsTour σ) :
    10 ≤ tourCost prismMetric σ := by
  have hv : ∀ i, ![σ 0, σ 1, σ 2, σ 3, σ 4, σ 5] i = σ i := by
    intro i; fin_cases i <;> rfl
  have hinj : ∀ i j : Fin 6, i ≠ j → σ i ≠ σ j := fun i j h h' => h (σ.injective h')
  have key := prism_tour_bound (σ 0) (hσ.apply_ne 0) (σ 1)
    ⟨hσ.apply_ne 1, hinj 1 0 (by decide)⟩ (σ 2)
    ⟨hσ.apply_ne 2, hinj 2 0 (by decide), hinj 2 1 (by decide)⟩ (σ 3)
    ⟨hσ.apply_ne 3, hinj 3 0 (by decide), hinj 3 1 (by decide), hinj 3 2 (by decide)⟩ (σ 4)
    ⟨hσ.apply_ne 4, hinj 4 0 (by decide), hinj 4 1 (by decide), hinj 4 2 (by decide),
      hinj 4 3 (by decide)⟩ (σ 5)
    ⟨hσ.apply_ne 5, hinj 5 0 (by decide), hinj 5 1 (by decide), hinj 5 2 (by decide),
      hinj 5 3 (by decide), hinj 5 4 (by decide)⟩
    (fun i => by rw [hv, hv]; exact hσ.apply_apply_ne (by norm_num) i)
  unfold tourCost prismMetric
  rw [Fin.sum_univ_six]
  exact_mod_cast key

theorem prism_optValue_ge : 10 ≤ optValue prismMetric := by
  obtain ⟨σ₀, hσ₀⟩ := exists_tour (n := 6) (by norm_num)
  refine le_csInf ⟨_, σ₀, hσ₀, rfl⟩ ?_
  rintro _ ⟨σ, hσ, rfl⟩
  exact prism_tourCost_ge hσ

theorem prism_lpValue_le : lpValue prismMetric ≤ 9 := by
  rw [← lpCost_prismFrac]
  exact csInf_le ⟨0, by rintro _ ⟨x, hx, rfl⟩; exact lpCost_nonneg prismMetric_isMetric hx⟩
    ⟨_, prismFrac_feasible, rfl⟩

theorem prism_lpCost_ge {x : Fin 6 → Fin 6 → ℝ} (hx : SubtourFeasible x) :
    6 ≤ lpCost prismMetric x := by
  have hterm : ∀ i j, x i j ≤ prismMetric i j * x i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp [hx.2.1 i]
    · have h1 : (1 : ℝ) ≤ prismMetric i j := by
        unfold prismMetric
        have : 1 ≤ prismD i j := by
          revert hij; revert i j; decide
        exact_mod_cast this
      nlinarith [(hx.2.2.1 i j).1]
  have hsum : ∑ i : Fin 6, ∑ j, x i j ≤ ∑ i, ∑ j, prismMetric i j * x i j :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
  simp only [hx.2.2.2.1, sum_const, card_univ, Fintype.card_fin] at hsum
  unfold lpCost; norm_num at hsum ⊢; linarith

theorem prism_lpValue_pos : 0 < lpValue prismMetric := by
  obtain ⟨σ₀, hσ₀⟩ := exists_tour (n := 6) (by norm_num)
  have : 6 ≤ lpValue prismMetric :=
    le_csInf ⟨_, _, tourVec_feasible hσ₀ (by norm_num), rfl⟩
      (by rintro _ ⟨x, hx, rfl⟩; exact prism_lpCost_ge hx)
  linarith

/-- **Known result** (the subtour LP has integrality gap `> 1`; the half-integral prism point is
the standard small example, cf. Benoit–Boyd, "Finding the exact integrality gap for small
traveling salesman problems", *Math. Oper. Res.* 33 (2008), who study gaps for `n ≤ 10`): for the prism metric `OPT ≥ 10` and
`LP ≤ 9`, so `gapSet` contains a ratio at least `10/9`. Only `10/9` is certified here; this is
far from deciding whether the gap equals `4/3`. -/
theorem exists_mem_gapSet_ge_ten_ninths : ∃ r ∈ gapSet, (10 : ℝ) / 9 ≤ r := by
  refine ⟨optValue prismMetric / lpValue prismMetric,
    ⟨6, prismMetric, by norm_num, prismMetric_isMetric, prism_lpValue_pos, rfl⟩, ?_⟩
  have hpos := prism_lpValue_pos
  rw [div_le_div_iff₀ (by norm_num) hpos]
  nlinarith [prism_optValue_ge, prism_lpValue_le]

/-- Consequence: any upper bound of `gapSet` (in particular the integrality gap) is at least
`10/9`. -/
theorem ten_ninths_le_of_mem_upperBounds {u : ℝ} (hu : u ∈ upperBounds gapSet) :
    (10 : ℝ) / 9 ≤ u := by
  obtain ⟨r, hr, hle⟩ := exists_mem_gapSet_ge_ten_ninths
  exact hle.trans (hu hr)

end CryptoLean.OpenProblems.LinearProgramming

section Axioms
open CryptoLean.OpenProblems.LinearProgramming
#print axioms weak_duality
#print axioms optimal_of_eq
#print axioms dual_optimal_of_eq
#print axioms expectedPivots_eq_zero_of_optimal
#print axioms tourVec_feasible
#print axioms lpCost_tourVec
#print axioms lpValue_le_optValue
#print axioms one_le_of_mem_gapSet
#print axioms exists_mem_gapSet_ge_ten_ninths
#print axioms ten_ninths_le_of_mem_upperBounds
end Axioms
