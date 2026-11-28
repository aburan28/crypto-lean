import Mathlib

/-!
# Kissing numbers: definitions, the exact-value problem, and root-system lower bounds

ProofAtlas problem #5, *Exact Kissing Numbers in Higher Dimensions*.

The kissing number `τ_n` is the largest number of non-overlapping congruent balls in `ℝⁿ`
that can all touch one further ball of the same radius.  If all balls have radius `r / 2`,
the touching balls have centres `v` with `‖v‖ = r`, and two of them do not overlap iff
`‖v - w‖ ≥ r`, i.e. (for `‖v‖ = ‖w‖ = r`) iff `2 ⟪v, w⟫ ≤ r²`, i.e. the angle between
`v` and `w` is at least `60°`.  This is the definition used below.

What is proved here (all **known results**):
* `kissing_of_int_family`: a family of integer vectors of common squared length `R` with
  pairwise dot products `≤ R / 2` gives a kissing configuration in `EuclideanSpace ℝ (Fin n)`.
* `kissingAtLeast_Dn`: the `D_n` root system (`±eᵢ ± eⱼ`) gives `τ_n ≥ 2n(n-1)`.
* `kissingAtLeast_five`: in particular `τ_5 ≥ 40` (the best known lower bound).
* `kissingAtLeast_eight`: the `E₈` root system gives `τ_8 ≥ 240`.

What is **not** proved here: any upper bound.  In particular the known exact values
`τ_8 = 240` and `τ_24 = 196560` (Levenshtein 1979; Odlyzko–Sloane 1979) and `τ_4 = 24`
(Musin 2008) are *not* formalised in this file; only the lower-bound halves for `n = 8`
(and the `D_n` bound for all `n`) are.  The exact value of `τ_5` is open
(`40 ≤ τ_5 ≤ 44`), and so are all `τ_n` for `n ∉ {1, 2, 3, 4, 8, 24}`.
-/

namespace CryptoLean.OpenProblems.Kissing

open Matrix Finset
open scoped RealInnerProductSpace

/-- Ambient Euclidean space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A **kissing configuration** in `ℝⁿ`: a finite set of centres `v`, all at the same distance
`r > 0` from the origin, pairwise at distance `≥ r`.  Equivalently, balls of radius `r / 2`
centred at the points of `S` all touch the ball of radius `r / 2` centred at `0`, and have
pairwise disjoint interiors. -/
def IsKissingConfiguration {n : ℕ} (S : Finset (E n)) : Prop :=
  ∃ r : ℝ, 0 < r ∧ (∀ v ∈ S, ‖v‖ = r) ∧ ∀ v ∈ S, ∀ w ∈ S, v ≠ w → r ≤ ‖v - w‖

/-- Angle formulation: for two centres of common norm `r`, being at distance `≥ r` is
equivalent to `2 ⟪v, w⟫ ≤ r²` (angle at least `60°`). -/
theorem le_norm_sub_iff {n : ℕ} {v w : E n} {r : ℝ} (hr : 0 ≤ r) (hv : ‖v‖ = r)
    (hw : ‖w‖ = r) : r ≤ ‖v - w‖ ↔ 2 * ⟪v, w⟫ ≤ r ^ 2 := by
  have h := norm_sub_sq_real v w
  rw [hv, hw] at h
  rw [← sq_le_sq₀ hr (norm_nonneg _), h]
  constructor <;> intro <;> linarith

/-- `τ_n ≥ k`: there is a kissing configuration in `ℝⁿ` with exactly `k` balls. -/
def KissingAtLeast (n k : ℕ) : Prop :=
  ∃ S : Finset (E n), IsKissingConfiguration S ∧ S.card = k

/-- `τ_n = k`: some kissing configuration has `k` balls and none has more. -/
def KissingNumberEq (n k : ℕ) : Prop :=
  KissingAtLeast n k ∧ ∀ S : Finset (E n), IsKissingConfiguration S → S.card ≤ k

/-- **Open problem (ProofAtlas #5, Exact Kissing Numbers in Higher Dimensions).**
The ProofAtlas statement asks to determine the exact kissing number `τ_n` in dimensions where
it is unknown, the first being `n = 5`, where `40 ≤ τ_5 ≤ 44` is all that is known
(lower bound from `D_5`, upper bound by semidefinite programming).  This file states the
first case as the conjecture `τ_5 = 40` (the value attained by `D_5`).

Modelling notes (honest): the ProofAtlas text was not available verbatim to the author of
this file, so the statement above is a paraphrase; a Prop cannot say "determine", so the
case `n = 5` is recorded as the specific conjectural value `40` — a proof that `τ_5 > 40`
would also resolve the problem, and would refute this Prop.  This is **not** proved here. -/
def KissingNumberFiveConjecture : Prop := KissingNumberEq 5 40

/-- **Open problem, general form.**  For every dimension `n` outside the solved list
`{1, 2, 3, 4, 8, 24}` the value of `τ_n` is unknown; this Prop says that `τ_n` equals a
proposed value `k`.  It is stated only as a template and is **not** proved here. -/
def ExactKissingNumber (n k : ℕ) : Prop := KissingNumberEq n k

/-! ### Transfer from integer vectors -/

/-- Integer vector, viewed in `ℝⁿ`. -/
def toE {n : ℕ} (v : Fin n → ℤ) : E n := WithLp.toLp 2 (fun i => (v i : ℝ))

theorem toE_injective {n : ℕ} : Function.Injective (toE (n := n)) := by
  intro v w h
  funext i
  have := congrArg (fun x : E n => x.ofLp i) h
  simpa [toE] using this

theorem inner_toE {n : ℕ} (v w : Fin n → ℤ) : ⟪toE v, toE w⟫ = ((v ⬝ᵥ w : ℤ) : ℝ) := by
  simp [toE, PiLp.inner_apply, dotProduct, mul_comm]

theorem norm_toE_sq {n : ℕ} (v : Fin n → ℤ) : ‖toE v‖ ^ 2 = ((v ⬝ᵥ v : ℤ) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_toE]

/-- **Transfer lemma.**  An indexed family of integer vectors of common squared length
`R > 0`, with `2 (fᵢ ⬝ fⱼ) ≤ R` for `i ≠ j`, gives a kissing configuration of size `|ι|`. -/
theorem kissing_of_int_family {n : ℕ} {ι : Type*} [Fintype ι] (f : ι → Fin n → ℤ) (R : ℤ)
    (hR : 0 < R) (hnorm : ∀ i, f i ⬝ᵥ f i = R)
    (hpair : ∀ i j, i ≠ j → 2 * (f i ⬝ᵥ f j) ≤ R) :
    KissingAtLeast n (Fintype.card ι) := by
  classical
  have hinj : Function.Injective f := by
    intro i j h
    by_contra hij
    have := hpair i j hij
    rw [h, hnorm] at this
    omega
  refine ⟨univ.image (toE ∘ f), ?_, ?_⟩
  · have hR' : (0 : ℝ) < R := by exact_mod_cast hR
    have hn : ∀ i, ‖toE (f i)‖ = Real.sqrt R := by
      intro i
      rw [← Real.sqrt_sq (norm_nonneg _), norm_toE_sq, hnorm]
    refine ⟨Real.sqrt R, Real.sqrt_pos.2 hR', ?_, ?_⟩
    · simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      rintro _ ⟨i, rfl⟩
      exact hn i
    · simp only [mem_image, mem_univ, true_and, Function.comp_apply]
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
      have hij : i ≠ j := by rintro rfl; exact hne rfl
      rw [le_norm_sub_iff (Real.sqrt_nonneg _) (hn i) (hn j), Real.sq_sqrt hR'.le, inner_toE]
      exact_mod_cast hpair i j hij
  · rw [card_image_of_injective _ (toE_injective.comp hinj), card_univ]

/-- Distinct integer vectors of squared length `2` have dot product at most `1`. -/
theorem two_mul_dot_le_of_norm_two {n : ℕ} {v w : Fin n → ℤ} (hv : v ⬝ᵥ v = 2)
    (hw : w ⬝ᵥ w = 2) (hne : v ≠ w) : 2 * (v ⬝ᵥ w) ≤ 2 := by
  have hpos : 0 < (v - w) ⬝ᵥ (v - w) := by
    have h0 : 0 ≤ (v - w) ⬝ᵥ (v - w) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 (dotProduct_self_eq_zero.1 h.symm)) hne
  have hexp : (v - w) ⬝ᵥ (v - w) = v ⬝ᵥ v - 2 * (v ⬝ᵥ w) + w ⬝ᵥ w := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w v]; ring
  rw [hexp, hv, hw] at hpos
  omega

/-! ### The `D_n` root system -/

/-- `±1` from a Boolean. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> rfl

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> decide

/-- Index set of `D_n`: a pair `i < j` and two signs. -/
abbrev DIdx (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2} × Bool × Bool

/-- The `D_n` root `sgn(a) eᵢ + sgn(b) eⱼ`. -/
def dRoot {n : ℕ} (x : DIdx n) : Fin n → ℤ :=
  Pi.single x.1.1.1 (sgn x.2.1) + Pi.single x.1.1.2 (sgn x.2.2)

theorem dRoot_apply {n : ℕ} (x : DIdx n) (k : Fin n) :
    dRoot x k = (if k = x.1.1.1 then sgn x.2.1 else 0) + (if k = x.1.1.2 then sgn x.2.2 else 0) := by
  simp [dRoot, Pi.single_apply]

theorem dRoot_dot_self {n : ℕ} (x : DIdx n) : dRoot x ⬝ᵥ dRoot x = 2 := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ := x
  have hne : i ≠ j := ne_of_lt hij
  simp only [dRoot, add_dotProduct, dotProduct_add, single_dotProduct, Pi.single_eq_same,
    Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
  simp [sgn_sq]

theorem dRoot_fst {n : ℕ} (x : DIdx n) : dRoot x x.1.1.1 = sgn x.2.1 := by
  have hne : x.1.1.1 ≠ x.1.1.2 := ne_of_lt x.1.2
  rw [dRoot_apply]; split_ifs <;> simp_all

theorem dRoot_snd {n : ℕ} (x : DIdx n) : dRoot x x.1.1.2 = sgn x.2.2 := by
  have hne : x.1.1.1 ≠ x.1.1.2 := ne_of_lt x.1.2
  rw [dRoot_apply]; split_ifs <;> simp_all

theorem dRoot_ne_zero {n : ℕ} (x : DIdx n) (k : Fin n) :
    dRoot x k ≠ 0 ↔ k = x.1.1.1 ∨ k = x.1.1.2 := by
  constructor
  · intro h
    by_contra h'
    push Not at h'
    apply h
    simp [dRoot_apply, h'.1, h'.2]
  · rintro (rfl | rfl)
    · rw [dRoot_fst]; exact sgn_ne_zero _
    · rw [dRoot_snd]; exact sgn_ne_zero _

theorem sgn_injective : Function.Injective sgn := by
  intro a b h; cases a <;> cases b <;> simp_all [sgn]

theorem dRoot_injective {n : ℕ} : Function.Injective (dRoot (n := n)) := by
  intro x y h
  have hs : ∀ k, (k = x.1.1.1 ∨ k = x.1.1.2) ↔ (k = y.1.1.1 ∨ k = y.1.1.2) := by
    intro k; rw [← dRoot_ne_zero, ← dRoot_ne_zero, h]
  obtain ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ := x
  obtain ⟨⟨⟨i', j'⟩, hij'⟩, a', b'⟩ := y
  have h1 := (hs i).1 (Or.inl rfl)
  have h2 := (hs j).1 (Or.inr rfl)
  have h3 := (hs i').2 (Or.inl rfl)
  have h4 := (hs j').2 (Or.inr rfl)
  simp only [Fin.ext_iff] at h1 h2 h3 h4
  have hlt : i.val < j.val := hij
  have hlt' : i'.val < j'.val := hij'
  have hi : i = i' := Fin.ext (by omega)
  have hj : j = j' := Fin.ext (by omega)
  subst hi hj
  have ha := dRoot_fst ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  have hb := dRoot_snd ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
  rw [h, dRoot_fst] at ha
  rw [h, dRoot_snd] at hb
  obtain rfl := sgn_injective ha
  obtain rfl := sgn_injective hb
  rfl

theorem card_DIdx (n : ℕ) : Fintype.card (DIdx n) = 2 * n * (n - 1) := by
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_subtype,
    Fintype.card_product_filter_lt, Fintype.card_fin, Fintype.card_bool, Nat.choose_two_right]
  obtain ⟨m, hm⟩ := Nat.even_mul_pred_self n
  have h2 : 2 * n * (n - 1) = 2 * (n * (n - 1)) := by ring
  rw [h2, hm]
  omega

/-- **`D_n` lower bound** (known result; see Conway–Sloane, *Sphere Packings, Lattices and
Groups*, Ch. 1, Table 1.5 and §4.7.3): the `2n(n-1)` minimal vectors `±eᵢ ± eⱼ` of the
`D_n` lattice form a kissing configuration, so `τ_n ≥ 2n(n-1)` for every `n`. -/
theorem kissingAtLeast_Dn (n : ℕ) : KissingAtLeast n (2 * n * (n - 1)) := by
  rw [← card_DIdx]
  refine kissing_of_int_family dRoot 2 (by norm_num) dRoot_dot_self ?_
  intro x y hxy
  exact two_mul_dot_le_of_norm_two (dRoot_dot_self x) (dRoot_dot_self y)
    (dRoot_injective.ne hxy)

/-- **`τ_5 ≥ 40`** (known result; `D_5`, see Conway–Sloane, *SPLAG*, Table 1.5).  This is the
best known lower bound; the exact value of `τ_5` remains open (`40 ≤ τ_5 ≤ 44`). -/
theorem kissingAtLeast_five : KissingAtLeast 5 40 := kissingAtLeast_Dn 5

/-- `τ_3 ≥ 12` from `D_3` (the face-centred cubic arrangement; known result, see Conway–Sloane,
*SPLAG*, Table 1.5; the matching upper bound, Schütte–van der Waerden 1953, is not proved
here). -/
theorem kissingAtLeast_three : KissingAtLeast 3 12 := kissingAtLeast_Dn 3

/-- `τ_4 ≥ 24` from `D_4` (known result; the matching upper bound is Musin 2008, not proved
here). -/
theorem kissingAtLeast_four : KissingAtLeast 4 24 := kissingAtLeast_Dn 4

/-! ### The `E₈` root system (scaled by `2`) -/

/-- The `E₈` minimal vector `(sgn s₀, …, sgn s₆, ∏ sgn sₖ)` (the 128 vectors `½(±1)⁸` with an
even number of minus signs, scaled by `2`). -/
def eHalf (s : Fin 7 → Bool) : Fin 8 → ℤ :=
  Fin.lastCases (∏ k, sgn (s k)) (fun k => sgn (s k))

theorem eHalf_castSucc (s : Fin 7 → Bool) (k : Fin 7) : eHalf s k.castSucc = sgn (s k) := by
  rw [eHalf, Fin.lastCases_castSucc]

theorem eHalf_last (s : Fin 7 → Bool) : eHalf s (Fin.last 7) = ∏ k, sgn (s k) := by
  rw [eHalf, Fin.lastCases_last]

theorem eHalf_pm (s : Fin 7 → Bool) (k : Fin 8) : eHalf s k = 1 ∨ eHalf s k = -1 := by
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [eHalf_last]
    refine Finset.prod_induction _ (fun x : ℤ => x = 1 ∨ x = -1) ?_ (Or.inl rfl) ?_
    · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
    · intro k _; cases s k <;> simp [sgn]
  · rw [eHalf_castSucc]; cases s k <;> simp [sgn]

theorem sgn_mul_sgn (a b : Bool) : sgn a * sgn b = sgn (a == b) := by
  cases a <;> cases b <;> rfl

theorem eHalf_dot (s t : Fin 7 → Bool) :
    eHalf s ⬝ᵥ eHalf t = ∑ k, sgn (s k == t k) + ∏ k, sgn (s k == t k) := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [eHalf_castSucc, eHalf_last, ← Finset.prod_mul_distrib, sgn_mul_sgn]

theorem eHalf_dot_self (s : Fin 7 → Bool) : eHalf s ⬝ᵥ eHalf s = 8 := by
  rw [eHalf_dot]; simp [sgn]

theorem seven_signs_aux : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
    (b0 && b1 && b2 && b3 && b4 && b5 && b6) = false →
    sgn b0 + sgn b1 + sgn b2 + sgn b3 + sgn b4 + sgn b5 + sgn b6 +
      sgn b0 * sgn b1 * sgn b2 * sgn b3 * sgn b4 * sgn b5 * sgn b6 ≤ 4 := by
  decide

/-- Parity core: seven signs, not all `+1`, have sum plus product at most `4`. -/
theorem seven_signs (u : Fin 7 → Bool) (hu : ∃ k, u k = false) :
    ∑ k, sgn (u k) + ∏ k, sgn (u k) ≤ 4 := by
  rw [Fin.sum_univ_seven, Fin.prod_univ_seven]
  apply seven_signs_aux
  obtain ⟨k, hk⟩ := hu
  fin_cases k <;> simp_all

theorem eHalf_pair (s t : Fin 7 → Bool) (hst : s ≠ t) : 2 * (eHalf s ⬝ᵥ eHalf t) ≤ 8 := by
  rw [eHalf_dot]
  have : ∃ k, (s k == t k) = false := by
    by_contra h
    push Not at h
    exact hst (funext fun k => by simpa using h k)
  have := seven_signs (fun k => s k == t k) this
  omega

/-- Index set of the `E₈` minimal vectors: `D₈` part (112) and half-integer part (128). -/
abbrev E8Idx := DIdx 8 ⊕ (Fin 7 → Bool)

/-- The 240 minimal vectors of `E₈`, scaled by `2` so that all coordinates are integers. -/
def e8Root : E8Idx → Fin 8 → ℤ
  | .inl x => (2 : ℤ) • dRoot x
  | .inr s => eHalf s

theorem mixed_dot (x : DIdx 8) (s : Fin 7 → Bool) : 2 * (((2 : ℤ) • dRoot x) ⬝ᵥ eHalf s) ≤ 8 := by
  obtain ⟨⟨⟨i, j⟩, hij⟩, a, b⟩ := x
  simp only [dRoot, smul_add, add_dotProduct, smul_dotProduct, single_dotProduct, smul_eq_mul]
  rcases eHalf_pm s i with h1 | h1 <;> rcases eHalf_pm s j with h2 | h2 <;> rw [h1, h2] <;>
    cases a <;> cases b <;> simp [sgn]

theorem card_E8Idx : Fintype.card E8Idx = 240 := by
  rw [Fintype.card_sum, card_DIdx]; simp

/-- **`τ_8 ≥ 240`** (known result; the `E₈` root system, see Conway–Sloane, *SPLAG*,
Ch. 4 §8.1 and Table 1.5).  The matching upper bound `τ_8 ≤ 240` (Levenshtein 1979;
Odlyzko–Sloane 1979) is a known result that is **not** formalised here. -/
theorem kissingAtLeast_eight : KissingAtLeast 8 240 := by
  rw [← card_E8Idx]
  refine kissing_of_int_family e8Root 8 (by norm_num) ?_ ?_
  · rintro (x | s)
    · simp only [e8Root, smul_dotProduct, dotProduct_smul, dRoot_dot_self, smul_eq_mul]; norm_num
    · exact eHalf_dot_self s
  · rintro (x | s) (y | t) hne
    · have hxy : x ≠ y := fun h => hne (h ▸ rfl)
      have := two_mul_dot_le_of_norm_two (dRoot_dot_self x) (dRoot_dot_self y)
        (dRoot_injective.ne hxy)
      simp only [e8Root, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      omega
    · exact mixed_dot x t
    · simp only [e8Root]; rw [dotProduct_comm]; exact mixed_dot y s
    · exact eHalf_pair s t (fun h => hne (h ▸ rfl))

end CryptoLean.OpenProblems.Kissing

#print axioms CryptoLean.OpenProblems.Kissing.le_norm_sub_iff
#print axioms CryptoLean.OpenProblems.Kissing.kissing_of_int_family
#print axioms CryptoLean.OpenProblems.Kissing.kissingAtLeast_Dn
#print axioms CryptoLean.OpenProblems.Kissing.kissingAtLeast_three
#print axioms CryptoLean.OpenProblems.Kissing.kissingAtLeast_four
#print axioms CryptoLean.OpenProblems.Kissing.kissingAtLeast_five
#print axioms CryptoLean.OpenProblems.Kissing.kissingAtLeast_eight
