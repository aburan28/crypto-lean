import CryptoLean.Curve.SubgroupDLog
import Mathlib.Algebra.Polynomial.Roots

/-!
# Degree bounds and a generic query bound with polynomial exceptions

A vanishing test has at most as many distinct roots as its degree. A degree
bound controls the exceptional inputs in the oracle comparison below. Circuit
size and degree are separate resources.
-/

set_option autoImplicit false

namespace CryptoLean.PrimeFieldBarrier

open Finset GenericDLog _root_.Polynomial

private theorem roots_card_le_degree {F : Type*} [Field F] [DecidableEq F] (f : F[X]) :
    f.roots.toFinset.card ≤ f.natDegree :=
  (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' f)

/-- A nonzero univariate vanishing test requires degree at least the number of accepted values. -/
theorem card_le_degree_of_vanishes {F : Type*} [Field F] [DecidableEq F] (s : Finset F)
    {f : F[X]} (hf : f ≠ 0) (hz : ∀ x ∈ s, f.eval x = 0) : s.card ≤ f.natDegree :=
  (Finset.card_le_card (show s ⊆ f.roots.toFinset from fun x hx =>
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr (hz x hx)))).trans
      (roots_card_le_degree f)

/-- A sequence of squarings, counted by its recursion index. -/
noncomputable def repeatSquaring {F : Type*} [Semiring F] (f : F[X]) : ℕ → F[X]
  | 0 => f
  | n + 1 => repeatSquaring f n ^ 2

theorem repeatSquaring_X_degree (F : Type*) [Field F] (n : ℕ) :
    (repeatSquaring (X : F[X]) n).natDegree = 2 ^ n := by
  have hx : repeatSquaring (X : F[X]) n = X ^ (2 ^ n) := by
    induction n with
    | zero => simp [repeatSquaring]
    | succ n ih => rw [repeatSquaring, ih, ← pow_mul, pow_succ]
  rw [hx, Polynomial.natDegree_X_pow]

section Exceptions

variable {r : ℕ} [Fact r.Prime] {ι : Type*} [Fintype ι]

/-- The union of roots of a finite family of exceptional-input polynomials. -/
noncomputable def polynomialExceptions (polynomials : ι → (ZMod r)[X]) : Finset (ZMod r) :=
  (univ : Finset ι).biUnion fun i => (polynomials i).roots.toFinset

theorem polynomialExceptions_card_le (polynomials : ι → (ZMod r)[X]) :
    (polynomialExceptions polynomials).card ≤ ∑ i, (polynomials i).natDegree := by
  calc
    _ ≤ ∑ i : ι, (polynomials i).roots.toFinset.card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum fun i _ => roots_card_le_degree (polynomials i)

private theorem eval_ne_zero_of_not_mem_polynomialExceptions (polynomials : ι → (ZMod r)[X])
    {x : ZMod r} (hx : x ∉ polynomialExceptions polynomials) {i : ι} (hi : polynomials i ≠ 0) :
    (polynomials i).eval x ≠ 0 := by
  intro hz
  exact hx (Finset.mem_biUnion.mpr ⟨i, mem_univ _,
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hi).mpr hz)⟩)

noncomputable def successfulSecrets (guess : ZMod r → ZMod r) : Finset (ZMod r) := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  exact univ.filter fun x => guess x = x

/-- Agreement with a generic run outside the polynomial roots bounds the extra successes. -/
theorem two_mul_success_le_of_polynomial_exceptions {View : ℕ → Type*} {q : ℕ}
    (observe : ∀ n, Pattern n → View n) (samples : ℕ → ZMod r)
    (strategy : Strategy r View 3 q) (guess : ZMod r → ZMod r)
    (polynomials : ι → (ZMod r)[X]) (hnonzero : ∀ i, polynomials i ≠ 0)
    (hmatch : ∀ x, (∀ i, (polynomials i).eval x ≠ 0) → guess x = scalarGuess observe samples strategy x) :
    2 * (successfulSecrets guess).card ≤ successNumerator q + 2 * ∑ i, (polynomials i).natDegree := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have hsub : successfulSecrets guess ⊆
      successSecrets observe samples strategy ∪ polynomialExceptions polynomials := by
    intro x hx
    apply Finset.mem_union.mpr
    by_cases hb : x ∈ polynomialExceptions polynomials
    · exact Or.inr hb
    · left
      have hg (i : ι) := eval_ne_zero_of_not_mem_polynomialExceptions polynomials hb (hnonzero i)
      unfold successfulSecrets at hx
      unfold GenericDLog.successSecrets
      exact Finset.mem_filter.mpr ⟨mem_univ _, (hmatch x hg).symm.trans (Finset.mem_filter.mp hx).2⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hg := two_mul_card_successSecrets_le observe samples strategy
  have hp := polynomialExceptions_card_le polynomials
  unfold successNumerator
  omega

/-- With independent finite random seeds, the degree term is the expected total degree. -/
theorem two_mul_expected_success_le_of_polynomial_exceptions {View : ℕ → Type*} {q : ℕ}
    {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ) (hnonneg : ∀ s, 0 ≤ weights s)
    (hnorm : ∑ s, weights s = 1) (observe : Seed → ∀ n, Pattern n → View n)
    (samples : Seed → ℕ → ZMod r) (strategy : Seed → Strategy r View 3 q)
    (guess : Seed → ZMod r → ZMod r) (polynomials : Seed → ι → (ZMod r)[X])
    (hnonzero : ∀ s i, polynomials s i ≠ 0)
    (hmatch : ∀ s x, (∀ i, (polynomials s i).eval x ≠ 0) →
      guess s x = scalarGuess (observe s) (samples s) (strategy s) x) :
    (∑ s, weights s * (2 * ((successfulSecrets (guess s)).card : ℝ))) ≤
      (successNumerator q : ℝ) + 2 * ∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ) := by
  have hseed (s : Seed) : 2 * ((successfulSecrets (guess s)).card : ℝ) ≤
      (successNumerator q : ℝ) + 2 * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ) := by
    exact_mod_cast two_mul_success_le_of_polynomial_exceptions (observe s) (samples s)
      (strategy s) (guess s) (polynomials s) (hnonzero s) (hmatch s)
  calc
    _ ≤ ∑ s, weights s * ((successNumerator q : ℝ) +
        2 * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ)) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hseed s) (hnonneg s)
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      ring

/-- At any cutoff, combine the mean actual query count and the mean exceptional degree.
Outside the roots, the reference run agrees with the solver and uses no more queries. -/
theorem mixed_success_le_of_polynomial_exceptions_with_expectedQueries {View : ℕ → Type*} {q : ℕ}
    {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ) (hnonneg : ∀ s, 0 ≤ weights s)
    (hnorm : ∑ s, weights s = 1) (observe : Seed → ∀ n, Pattern n → View n)
    (samples : Seed → ℕ → ZMod r) (strategy : Seed → Strategy r View 3 q)
    (guess : Seed → ZMod r → ZMod r) (count : Seed → ZMod r → ℕ)
    (polynomials : Seed → ι → (ZMod r)[X]) (hnonzero : ∀ s i, polynomials s i ≠ 0)
    (hmatch : ∀ s x, (∀ i, (polynomials s i).eval x ≠ 0) →
      guess s x = scalarGuess (observe s) (samples s) (strategy s) x ∧
      scalarQueryCount (observe s) (samples s) (strategy s) x ≤ count s x) (cutoff : ℕ) :
    (∑ s, weights s * ((successfulSecrets (guess s)).card : ℝ)) / (r : ℝ) ≤
      (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
        (∑ s, weights s * expectedQueries (count s)) / ((cutoff : ℝ) + 1) +
        (∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ)) / (r : ℝ) := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  refine mixed_card_div_le_of_truncation weights hnonneg hnorm observe samples strategy cutoff
    (fun s => successfulSecrets (guess s)) (fun s => polynomialExceptions (polynomials s)) count
    (fun s => ∑ i, (polynomials s i).natDegree) (fun s => polynomialExceptions_card_le (polynomials s)) ?_
  intro s x hx hgood
  obtain ⟨hguess, hcount⟩ := hmatch s x
    (fun i => eval_ne_zero_of_not_mem_polynomialExceptions (polynomials s) hgood (hnonzero s i))
  exact ⟨hguess.symm.trans (mem_filter.mp hx).2, hcount⟩

/-- Half success with mean exceptional degree at most `r / 4` forces a square-root mean query bound. -/
theorem sqrt_order_div_eight_le_of_half_success_with_polynomial_exceptions {View : ℕ → Type*} {q : ℕ}
    {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ) (hnonneg : ∀ s, 0 ≤ weights s)
    (hnorm : ∑ s, weights s = 1) (observe : Seed → ∀ n, Pattern n → View n)
    (samples : Seed → ℕ → ZMod r) (strategy : Seed → Strategy r View 3 q)
    (guess : Seed → ZMod r → ZMod r) (count : Seed → ZMod r → ℕ)
    (polynomials : Seed → ι → (ZMod r)[X]) (hnonzero : ∀ s i, polynomials s i ≠ 0)
    (hmatch : ∀ s x, (∀ i, (polynomials s i).eval x ≠ 0) →
      guess s x = scalarGuess (observe s) (samples s) (strategy s) x ∧
      scalarQueryCount (observe s) (samples s) (strategy s) x ≤ count s x)
    (hdegree : 4 * ∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ) ≤ (r : ℝ))
    (hsuccess : (1 : ℝ) / 2 ≤
      (∑ s, weights s * ((successfulSecrets (guess s)).card : ℝ)) / (r : ℝ)) :
    Real.sqrt ((r : ℝ) / 8) ≤ 8 * (∑ s, weights s * expectedQueries (count s)) + 2 := by
  let mean := ∑ s, weights s * expectedQueries (count s)
  let degree := ∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ)
  have hr : (0 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).pos
  have hmean : 0 ≤ mean := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hnonneg s) (by unfold expectedQueries; positivity)
  have hdegreeFraction : degree / (r : ℝ) ≤ 1 / 4 :=
    (div_le_iff₀ hr).mpr (by change 4 * degree ≤ (r : ℝ) at hdegree; linarith only [hdegree])
  have hcutoffs (cutoff : ℕ) : (1 : ℝ) / 4 ≤ (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
      mean / ((cutoff : ℝ) + 1) := by
    have htotal := hsuccess.trans (mixed_success_le_of_polynomial_exceptions_with_expectedQueries
      weights hnonneg hnorm observe samples strategy guess count polynomials hnonzero hmatch cutoff)
    change (1 : ℝ) / 2 ≤ _ + mean / ((cutoff : ℝ) + 1) + degree / (r : ℝ) at htotal
    linarith only [htotal, hdegreeFraction]
  have h := sqrt_success_mul_order_div_two_le_of_cutoffs (Fact.out : r.Prime).pos (by norm_num) hmean hcutoffs
  have hscale : (1 : ℝ) / 4 * (r : ℝ) / 2 = (r : ℝ) / 8 := by ring
  rw [hscale] at h
  calc
    _ ≤ 2 * mean / (1 / 4) + 2 := h
    _ = _ := by change 2 * mean / (1 / 4) + 2 = 8 * mean + 2; ring

/-- The half-success bound only needs a cap on expected exceptional degree. -/
theorem order_le_twice_successNumerator_of_expected_half {r q : ℕ}
    {twiceExpectedSolved expectedDegree : ℝ} (hsuccess : (r : ℝ) ≤ twiceExpectedSolved)
    (hcount : twiceExpectedSolved ≤ (successNumerator q : ℝ) + 2 * expectedDegree)
    (hdegree : 4 * expectedDegree ≤ (r : ℝ)) : r ≤ 2 * successNumerator q := by
  have h : (r : ℝ) ≤ 2 * (successNumerator q : ℝ) := by linarith only [hsuccess, hcount, hdegree]
  exact_mod_cast h

/-- A program selected by fixed preliminary zero tests satisfies the exceptional-set hypothesis. -/
theorem two_mul_success_le_of_preliminary_zero_tests {View : ℕ → Type*} {q : ℕ}
    (observe : ∀ n, Pattern n → View n) (samples : ℕ → ZMod r)
    (select : (ι → Bool) → Strategy r View 3 q)
    (polynomials : ι → (ZMod r)[X]) (hnonzero : ∀ i, polynomials i ≠ 0) :
    2 * (successfulSecrets (fun x => scalarGuess observe samples
      (select (fun i => decide ((polynomials i).eval x = 0))) x)).card ≤
      successNumerator q + 2 * ∑ i, (polynomials i).natDegree := by
  apply two_mul_success_le_of_polynomial_exceptions observe samples (select (fun _ => false)) _
    polynomials hnonzero
  intro x hx
  have htests : (fun i => decide ((polynomials i).eval x = 0)) = (fun _ => false) := by
    funext i
    simp [hx i]
  simp only [htests]

/-- With total exceptional degree at most `r / 4`, half success forces the query bound. -/
theorem order_le_twice_successNumerator_of_half {View : ℕ → Type*} {q : ℕ}
    (observe : ∀ n, Pattern n → View n) (samples : ℕ → ZMod r)
    (strategy : Strategy r View 3 q) (guess : ZMod r → ZMod r)
    (polynomials : ι → (ZMod r)[X]) (hnonzero : ∀ i, polynomials i ≠ 0)
    (hmatch : ∀ x, (∀ i, (polynomials i).eval x ≠ 0) → guess x = scalarGuess observe samples strategy x)
    (hdegree : 4 * ∑ i, (polynomials i).natDegree ≤ r)
    (hsuccess : r ≤ 2 * (successfulSecrets guess).card) : r ≤ 2 * successNumerator q := by
  have hb := two_mul_success_le_of_polynomial_exceptions observe samples strategy guess
    polynomials hnonzero hmatch
  omega

end Exceptions

/-- Convert the subgroup bound into a prime-field bound using Hasse and a cofactor cap. -/
theorem prime_field_query_bound {p r q H : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] (P : W.toAffine.Point) (horder : addOrderOf P = r) (hH : 0 < H)
    (hcofactor : ECDLP.cofactor P ≤ H) (hHasse : ECDLP.SatisfiesHasse p (Nat.card W.toAffine.Point))
    (hbudget : r ≤ 2 * successNumerator q) :
    Real.sqrt ((Real.sqrt p - 1) ^ 2 / (2 * (H : ℝ)) - 2) ≤ (q : ℝ) + 3 := by
  have hcount : Nat.card W.toAffine.Point ≤ (2 * H) * successNumerator q := by
    rw [← ECDLP.cofactor_mul_order P, horder]
    calc
      _ ≤ H * (2 * successNumerator q) := Nat.mul_le_mul hcofactor hbudget
      _ = _ := by ac_rfl
  have hpc := (ECDLP.pointCount_in_field_interval (lower := p) (upper := p)
    (Fact.out : p.Prime).pos le_rfl le_rfl hHasse).1
  have hc : (Nat.card W.toAffine.Point : ℝ) ≤ ((2 * H : ℕ) : ℝ) * (successNumerator q : ℝ) := by
    exact_mod_cast hcount
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    ECDLP.sqrt_field_lower_bound_le_budget (Nat.mul_pos two_pos hH) (hpc.trans hc)

/-- Half success with bounded expected exceptional degree gives the prime-field query bound. -/
theorem prime_field_query_bound_of_expected_half {p r q H : ℕ} [Fact p.Prime] [Fact r.Prime]
    (W : WeierstrassCurve (ZMod p)) [W.IsElliptic] (P : W.toAffine.Point)
    (horder : addOrderOf P = r) (hH : 0 < H) (hcofactor : ECDLP.cofactor P ≤ H)
    (hHasse : ECDLP.SatisfiesHasse p (Nat.card W.toAffine.Point))
    {View : ℕ → Type*} {Seed ι : Type*} [Fintype Seed] [Fintype ι]
    (weights : Seed → ℝ) (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) (guess : Seed → ZMod r → ZMod r)
    (polynomials : Seed → ι → (ZMod r)[X]) (hnonzero : ∀ s i, polynomials s i ≠ 0)
    (hmatch : ∀ s x, (∀ i, (polynomials s i).eval x ≠ 0) →
      guess s x = scalarGuess (observe s) (samples s) (strategy s) x)
    (hdegree : 4 * ∑ s, weights s * ((∑ i, (polynomials s i).natDegree : ℕ) : ℝ) ≤ (r : ℝ))
    (hsuccess : (1 : ℝ) / 2 ≤
      (∑ s, weights s * ((successfulSecrets (guess s)).card : ℝ)) / (r : ℝ)) :
    Real.sqrt ((Real.sqrt p - 1) ^ 2 / (2 * (H : ℝ)) - 2) ≤ (q : ℝ) + 3 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).pos
  have hscale : (∑ s, weights s * (2 * ((successfulSecrets (guess s)).card : ℝ))) =
      2 * ∑ s, weights s * ((successfulSecrets (guess s)).card : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => by ring)
  have hhalf : (r : ℝ) ≤ ∑ s, weights s * (2 * ((successfulSecrets (guess s)).card : ℝ)) := by
    rw [hscale]
    linarith only [(le_div_iff₀ hr).mp hsuccess]
  have hcount := two_mul_expected_success_le_of_polynomial_exceptions weights hnonneg hnorm
    observe samples strategy guess polynomials hnonzero hmatch
  exact prime_field_query_bound W P horder hH hcofactor hHasse
    (order_le_twice_successNumerator_of_expected_half hhalf hcount hdegree)

/-- Arithmetic specialization of the SGGM success estimate to a group of prime order `r`.
The success estimate is supplied as a hypothesis. -/
theorem sggm_half_success_tradeoff {r q : ℕ} {δ : ℝ} (hr : 0 < r)
    (hestimate : (1 : ℝ) / 2 ≤ δ * (3 * (q : ℝ) + 2) +
      (3 * (q : ℝ) + 1) ^ 2 / (r : ℝ) + 1 / (r : ℝ)) :
    (1 : ℝ) / 4 ≤ δ * (3 * (q : ℝ) + 2) ∨ Real.sqrt r / 2 ≤ 3 * (q : ℝ) + 2 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : (0 : ℝ) ≤ q := by positivity
  rcases le_or_gt ((1 : ℝ) / 4) (δ * (3 * (q : ℝ) + 2)) with h | h
  · exact Or.inl h
  · right
    by_contra! hsmall
    have hsquare := pow_lt_pow_left₀ hsmall (by positivity : 0 ≤ 3 * (q : ℝ) + 2)
      (by decide : (2 : ℕ) ≠ 0)
    have hsqrt := Real.sq_sqrt hr'.le
    have hnum : (3 * (q : ℝ) + 1) ^ 2 + 1 ≤ (3 * (q : ℝ) + 2) ^ 2 := by
      nlinarith only [hq]
    have hquarter : ((3 * (q : ℝ) + 1) ^ 2 + 1) / (r : ℝ) < 1 / 4 :=
      (div_lt_iff₀ hr').mpr (by nlinarith only [hsquare, hsqrt, hnum])
    rw [add_div] at hquarter
    linarith only [h, hquarter, hestimate]

def affineX {F : Type*} [Field F] (W : WeierstrassCurve F) : W.toAffine.Point → Option F
  | .zero => none
  | .some x _ _ => some x

@[simp] theorem affineX_neg {F : Type*} [Field F] (W : WeierstrassCurve F) (R : W.toAffine.Point) :
    affineX W (-R) = affineX W R := by cases R <;> rfl

/-- The affine x-coordinate cannot recover all signed scalars of an odd-order subgroup. -/
theorem no_signed_decoder_from_affine_x {F : Type*} [Field F] [DecidableEq F] {r : ℕ}
    [Fact r.Prime] (W : WeierstrassCurve F) [W.IsElliptic] (P : W.toAffine.Point)
    (horder : addOrderOf P = r) (hr : r ≠ 2) (readout : Option F → ZMod r) :
    ¬ ∀ k, readout (affineX W (ECDLP.scalarToPoint P horder k)) = k := by
  intro h
  have hneg := h (-(1 : ZMod r))
  rw [map_neg, affineX_neg] at hneg
  have heq : (1 : ZMod r) = -1 := (h 1).symm.trans hneg
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff 2 r).mp hz
    exact hr ((Nat.dvd_prime Nat.prime_two).mp hdiv |>.resolve_left (Fact.out : r.Prime).ne_one)
  exact htwo (by linear_combination heq)

end CryptoLean.PrimeFieldBarrier
