import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A generic discrete logarithm query bound

The oracle gives the algorithm handles for `0`, `P`, and `x • P`. An adaptive query can
append a linear combination of two existing handles or an independent sample. The algorithm's
observations are functions of the equality pattern of the handles. This allows opaque labels
assigned from a tape fixed independently of `x`.

Run the same program on affine forms in `x`. Outside the roots of pairwise collisions in
that symbolic execution, the real execution follows the same branches and gives one fixed guess.
-/

set_option autoImplicit false

namespace CryptoLean.GenericDLog

open Finset

abbrev Pattern (n : ℕ) := Fin n → Fin n → Bool

inductive Query (r n : ℕ) where
  | linear (i j : Fin n) (a b : ZMod r)
  | sample

/-- `Strategy r View n q` has `n` handles and can make at most `q` further queries. -/
inductive Strategy (r : ℕ) (View : ℕ → Type*) : ℕ → ℕ → Type _ where
  | finish {n q} (guess : View n → ZMod r) : Strategy r View n q
  | query {n q} (choose : View n → Query r n) (next : View n → Strategy r View (n + 1) q) :
      Strategy r View n (q + 1)

abbrev Oracle (r : ℕ) (V : Type*) := ∀ n, Query r n → (Fin n → V) → V

/-- All handles remain in the table throughout a run. -/
structure Execution (r : ℕ) (V : Type*) where
  size : ℕ
  table : Fin size → V
  answer : ZMod r

def equalityPattern {V : Type*} [DecidableEq V] {n : ℕ} (table : Fin n → V) : Pattern n :=
  fun i j => decide (table i = table j)

private def matchingIndices {n : ℕ} (pattern : Pattern n) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => pattern j i = true

private theorem self_mem_matchingIndices {V : Type*} [DecidableEq V] {n : ℕ}
    (table : Fin n → V) (i : Fin n) : i ∈ matchingIndices (equalityPattern table) i := by
  simp [matchingIndices, equalityPattern]

/-- Label each handle using the tape entry at the first occurrence of its value. -/
def labelsFromTape {Label : Type*} (tape : ℕ → Label) (n : ℕ) (pattern : Pattern n) : Fin n → Label :=
  fun i =>
    let candidates := matchingIndices pattern i
    if h : candidates.Nonempty then tape (candidates.min' h).val else tape i.val

theorem labelsFromTape_eq_iff {Label V : Type*} [DecidableEq V] {n : ℕ} (tape : ℕ → Label)
    (htape : Set.InjOn tape (Set.Iio n)) (table : Fin n → V) (i j : Fin n) :
    labelsFromTape tape n (equalityPattern table) i = labelsFromTape tape n (equalityPattern table) j
      ↔ table i = table j := by
  let S (k : Fin n) := matchingIndices (equalityPattern table) k
  have hs (k : Fin n) : (S k).Nonempty := ⟨k, self_mem_matchingIndices table k⟩
  let first (k : Fin n) := (S k).min' (hs k)
  have hm (k : Fin n) : first k ∈ S k := Finset.min'_mem _ _
  have he (k : Fin n) : table (first k) = table k := by
    simpa [S, matchingIndices, equalityPattern] using hm k
  have hlabel (k : Fin n) : labelsFromTape tape n (equalityPattern table) k = tape (first k).val := by
    unfold labelsFromTape
    exact dite_eq_left (hs k)
  rw [hlabel i, hlabel j]
  constructor
  · intro h
    have hfirst : first i = first j := Fin.ext (htape (first i).isLt (first j).isLt h)
    rw [← he i, ← he j, hfirst]
  · intro h
    have heq : S i = S j := by
      ext k
      simp [S, matchingIndices, equalityPattern, h]
    have hle : first i ≤ first j := Finset.min'_le _ _ (heq ▸ hm j)
    have hge : first j ≤ first i := Finset.min'_le _ _ (heq ▸ hm i)
    rw [le_antisymm hle hge]

/-- Appending a handle preserves every label previously issued by the tape. -/
theorem labelsFromTape_snoc {Label V : Type*} [DecidableEq V] {n : ℕ} (tape : ℕ → Label)
    (table : Fin n → V) (value : V) (i : Fin n) :
    labelsFromTape tape (n + 1) (equalityPattern (Fin.snoc table value)) i.castSucc =
      labelsFromTape tape n (equalityPattern table) i := by
  let old := matchingIndices (equalityPattern table) i
  let extended := matchingIndices (equalityPattern (Fin.snoc table value)) i.castSucc
  have hold : old.Nonempty := ⟨i, self_mem_matchingIndices table i⟩
  have hnew : extended.Nonempty := ⟨i.castSucc, self_mem_matchingIndices _ _⟩
  let first := old.min' hold
  let firstNew := extended.min' hnew
  have hcast (j : Fin n) : j.castSucc ∈ extended ↔ j ∈ old := by
    simp [old, extended, matchingIndices, equalityPattern]
  have hf : firstNew ≤ first.castSucc :=
    Finset.min'_le _ _ ((hcast first).mpr (Finset.min'_mem _ _))
  have hn : firstNew ≠ Fin.last n := ne_of_lt (hf.trans_lt (Fin.castSucc_lt_last _))
  obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hn
  have hjmem : j ∈ old := (hcast j).mp (hj ▸ Finset.min'_mem _ _)
  have he : firstNew = first.castSucc := by
    apply le_antisymm hf
    rw [← hj, Fin.castSucc_le_castSucc_iff]
    exact Finset.min'_le _ _ hjmem
  unfold labelsFromTape
  rw [dite_eq_left hnew, dite_eq_left hold]
  change tape firstNew.val = tape first.val
  rw [he]
  rfl

def run {r : ℕ} {V : Type*} [DecidableEq V] {View : ℕ → Type*}
    (observe : ∀ n, Pattern n → View n) (oracle : Oracle r V) {n q : ℕ}
    (strategy : Strategy r View n q) (table : Fin n → V) : Execution r V :=
  match strategy with
  | .finish guess => ⟨n, table, guess (observe n (equalityPattern table))⟩
  | .query choose next =>
    let view := observe n (equalityPattern table)
    run observe oracle (next view) (Fin.snoc table (oracle n (choose view) table))
termination_by q

theorem run_size_le {r : ℕ} {V : Type*} [DecidableEq V] {View : ℕ → Type*}
    (observe : ∀ n, Pattern n → View n) (oracle : Oracle r V) {n q : ℕ}
    (strategy : Strategy r View n q) (table : Fin n → V) :
    (run observe oracle strategy table).size ≤ n + q := by
  induction q generalizing n with
  | zero => cases strategy; simp [run]
  | succ q ih =>
    cases strategy with
    | finish => simp [run]
    | query choose next =>
      rw [run]
      let view := observe n (equalityPattern table)
      have h := ih (next view) (Fin.snoc table (oracle n (choose view) table))
      change (run observe oracle (next view) (Fin.snoc table (oracle n (choose view) table))).size ≤ _
      omega

theorem run_contains_table {r : ℕ} {V : Type*} [DecidableEq V] {View : ℕ → Type*}
    (observe : ∀ n, Pattern n → View n) (oracle : Oracle r V) {n q : ℕ}
    (strategy : Strategy r View n q) (table : Fin n → V) :
    Set.range table ⊆ Set.range (run observe oracle strategy table).table := by
  induction q generalizing n with
  | zero =>
    cases strategy
    rw [run]
  | succ q ih =>
    cases strategy with
    | finish => rw [run]
    | query choose next =>
      rw [run]
      rintro _ ⟨i, rfl⟩
      exact ih _ _ ⟨i.castSucc, Fin.snoc_castSucc _ _ _⟩

private theorem equalityPattern_map {A B : Type*} [DecidableEq A] [DecidableEq B]
    {n : ℕ} (table : Fin n → A) (f : A → B) (hf : Set.InjOn f (Set.range table)) :
    equalityPattern (f ∘ table) = equalityPattern table := by
  funext i j
  unfold equalityPattern
  exact decide_eq_decide.mpr ⟨fun h => hf ⟨i, rfl⟩ ⟨j, rfl⟩ h, congrArg f⟩

/-- If observations are preserved on the final table, map the entire adaptive execution. -/
theorem run_answer_eq_of_injOn {r : ℕ} {A B : Type*} [DecidableEq A] [DecidableEq B]
    {View : ℕ → Type*} (observe : ∀ n, Pattern n → View n) (oracleA : Oracle r A)
    (oracleB : Oracle r B) (f : A → B)
    (hmap : ∀ n cmd (table : Fin n → A), f (oracleA n cmd table) = oracleB n cmd (f ∘ table))
    {n q : ℕ} (strategy : Strategy r View n q) (table : Fin n → A)
    (hinj : Set.InjOn f (Set.range (run observe oracleA strategy table).table)) :
    (run observe oracleB strategy (f ∘ table)).answer = (run observe oracleA strategy table).answer := by
  induction q generalizing n with
  | zero =>
    cases strategy with
    | finish guess =>
      rw [run] at hinj
      simp only [run, equalityPattern_map table f hinj]
  | succ q ih =>
    have hpat := equalityPattern_map table f (hinj.mono (run_contains_table observe oracleA strategy table))
    cases strategy with
    | finish guess => simp only [run, hpat]
    | query choose next =>
      rw [run] at hinj
      simp only [run, hpat]
      let view := observe n (equalityPattern table)
      have htable : Fin.snoc (f ∘ table) (oracleB n (choose view) (f ∘ table)) =
          f ∘ Fin.snoc table (oracleA n (choose view) table) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [Function.comp_def] using (hmap n (choose view) table).symm
        · simp [Function.comp_def]
      change (run observe oracleB (next view) (Fin.snoc (f ∘ table) _)).answer =
        (run observe oracleA (next view) (Fin.snoc table _)).answer
      rw [htable]
      exact ih _ _ hinj

/-- The constant and linear coefficients of a handle's formal discrete logarithm. -/
abbrev Affine (r : ℕ) := ZMod r × ZMod r

def eval {r : ℕ} (x : ZMod r) (f : Affine r) : ZMod r := f.1 + f.2 * x

def symbolicOracle (r : ℕ) (samples : ℕ → ZMod r) : Oracle r (Affine r) := fun n cmd table =>
  match cmd with
  | .linear i j a b =>
    (a * (table i).1 + b * (table j).1, a * (table i).2 + b * (table j).2)
  | .sample => (samples n, 0)

def scalarOracle (r : ℕ) (samples : ℕ → ZMod r) : Oracle r (ZMod r) := fun n cmd table =>
  match cmd with
  | .linear i j a b => a * table i + b * table j
  | .sample => samples n

theorem eval_symbolicOracle {r : ℕ} (samples : ℕ → ZMod r) (x : ZMod r)
    (n : ℕ) (cmd : Query r n) (table : Fin n → Affine r) :
    eval x (symbolicOracle r samples n cmd table) = scalarOracle r samples n cmd (eval x ∘ table) := by
  cases cmd with
  | linear => simp [symbolicOracle, scalarOracle, eval]; ring
  | sample => simp [symbolicOracle, scalarOracle, eval]

def startingForms (r : ℕ) : Fin 3 → Affine r := ![(0, 0), (1, 0), (0, 1)]

section PrimeOrder

variable {r : ℕ} [Fact r.Prime]

private theorem eval_eq_at_most_one {f g : Affine r} (hne : f ≠ g)
    {x y : ZMod r} (hx : eval x f = eval x g) (hy : eval y f = eval y g) : x = y := by
  by_cases h : f.2 = g.2
  · unfold eval at hx
    rw [h] at hx
    exact (hne (Prod.ext (add_right_cancel hx) h)).elim
  · unfold eval at hx hy
    have he : (f.2 - g.2) * (x - y) = 0 := by linear_combination hx - hy
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h))

/-- All possible collisions between distinct affine forms in a symbolic execution. -/
def collisionSecrets {m : ℕ} (table : Fin m → Affine r) : Finset (ZMod r) :=
  letI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  (univ.filter fun ij : Fin m × Fin m => ij.1 < ij.2).biUnion fun ij =>
    univ.filter fun x => table ij.1 ≠ table ij.2 ∧ eval x (table ij.1) = eval x (table ij.2)

theorem mem_collisionSecrets {m : ℕ} (table : Fin m → Affine r) (x : ZMod r) :
    x ∈ collisionSecrets table ↔ ∃ i j : Fin m,
      i < j ∧ table i ≠ table j ∧ eval x (table i) = eval x (table j) := by
  simp [collisionSecrets]

theorem eval_injOn_of_no_collision {m : ℕ} (table : Fin m → Affine r) {x : ZMod r}
    (hx : x ∉ collisionSecrets table) : Set.InjOn (eval x) (Set.range table) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
  by_contra hne
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact hx ((mem_collisionSecrets table x).mpr ⟨i, j, hlt, hne, h⟩)
  · exact hne rfl
  · exact hx ((mem_collisionSecrets table x).mpr ⟨j, i, hgt, Ne.symm hne, h.symm⟩)

private theorem two_mul_card_increasingPairs_le (m : ℕ) :
    2 * (univ.filter fun ij : Fin m × Fin m => ij.1 < ij.2).card ≤ m * (m - 1) := by
  have he := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin m)))
  simp only [Finset.univ_product_univ, Finset.card_univ, Fintype.card_fin] at he
  rw [he, Nat.choose_two_right]
  omega

theorem two_mul_card_collisionSecrets_le {m : ℕ} (table : Fin m → Affine r) :
    2 * (collisionSecrets table).card ≤ m * (m - 1) := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  let pairs := univ.filter fun ij : Fin m × Fin m => ij.1 < ij.2
  let hits (ij : Fin m × Fin m) := univ.filter fun x =>
    table ij.1 ≠ table ij.2 ∧ eval x (table ij.1) = eval x (table ij.2)
  have hone (ij : Fin m × Fin m) : (hits ij).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [hits, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact eval_eq_at_most_one hx.1 hx.2 hy.2
  have hcard : (collisionSecrets table).card ≤ pairs.card := calc
    (collisionSecrets table).card = (pairs.biUnion hits).card := rfl
    _ ≤ ∑ ij ∈ pairs, (hits ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ pairs, 1 := Finset.sum_le_sum (fun ij _ => hone ij)
    _ = pairs.card := by simp
  exact (Nat.mul_le_mul_left 2 hcard).trans (two_mul_card_increasingPairs_le m)

variable {View : ℕ → Type*} (observe : ∀ n, Pattern n → View n) (samples : ℕ → ZMod r) {q : ℕ}

def scalarGuess (strategy : Strategy r View 3 q) (x : ZMod r) : ZMod r :=
  (run observe (scalarOracle r samples) strategy (eval x ∘ startingForms r)).answer

noncomputable def successSecrets (strategy : Strategy r View 3 q) : Finset (ZMod r) := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  exact univ.filter fun x => scalarGuess observe samples strategy x = x

/-- An adaptive algorithm with `q` queries can succeed on at most `choose (q + 3) 2 + 1` secrets. -/
theorem two_mul_card_successSecrets_le (strategy : Strategy r View 3 q) :
    2 * (successSecrets observe samples strategy).card ≤ (q + 3) * (q + 2) + 2 := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  let transcript := run observe (symbolicOracle r samples) strategy (startingForms r)
  have hsub : successSecrets observe samples strategy ⊆
      insert transcript.answer (collisionSecrets transcript.table) := by
    intro x hx
    by_cases hbad : x ∈ collisionSecrets transcript.table
    · exact Finset.mem_insert_of_mem hbad
    · apply Finset.mem_insert.mpr
      left
      have heq := run_answer_eq_of_injOn observe (symbolicOracle r samples) (scalarOracle r samples)
        (eval x) (eval_symbolicOracle samples x) strategy (startingForms r)
        (eval_injOn_of_no_collision transcript.table hbad)
      exact ((Finset.mem_filter.mp hx).2).symm.trans heq
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hbad := two_mul_card_collisionSecrets_le transcript.table
  have hsize : transcript.size ≤ q + 3 := by
    simpa [Nat.add_comm] using run_size_le observe (symbolicOracle r samples) strategy (startingForms r)
  have hp : transcript.size * (transcript.size - 1) ≤ (q + 3) * (q + 2) :=
    Nat.mul_le_mul hsize (by omega)
  omega

/-- Success probability for a uniformly distributed secret in `ZMod r`. -/
noncomputable def successProbability (strategy : Strategy r View 3 q) : ℝ :=
  ((successSecrets observe samples strategy).card : ℝ) / r

end PrimeOrder

/-- Twice the maximum number of uniform secrets covered by the collision argument. -/
def successNumerator (q : ℕ) : ℕ := (q + 3) * (q + 2) + 2

section Probability

variable {r : ℕ} [Fact r.Prime] {View : ℕ → Type*} {q : ℕ}

theorem successProbability_le (observe : ∀ n, Pattern n → View n) (samples : ℕ → ZMod r)
    (strategy : Strategy r View 3 q) :
    successProbability observe samples strategy ≤ (successNumerator q : ℝ) / (2 * (r : ℝ)) := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast (Fact.out : r.Prime).pos
  apply (le_div_iff₀ (mul_pos two_pos hr)).mpr
  unfold successProbability
  have he : ((successSecrets observe samples strategy).card : ℝ) / r * (2 * (r : ℝ)) =
      2 * ((successSecrets observe samples strategy).card : ℝ) := by
    field_simp
  rw [he]
  exact_mod_cast two_mul_card_successSecrets_le observe samples strategy

/-- Each seed fixes the program, the observations, and the independent sample tape. -/
noncomputable def mixedSuccessProbability {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) : ℝ :=
  ∑ s, weights s * successProbability (observe s) (samples s) (strategy s)

theorem mixedSuccessProbability_le {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) :
    mixedSuccessProbability weights observe samples strategy ≤
      (successNumerator q : ℝ) / (2 * (r : ℝ)) := by
  calc
    mixedSuccessProbability weights observe samples strategy ≤
        ∑ s, weights s * ((successNumerator q : ℝ) / (2 * (r : ℝ))) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (successProbability_le (observe s) (samples s) (strategy s)) (hnonneg s)
    _ = _ := by rw [← Finset.sum_mul, hnorm, one_mul]

end Probability

theorem order_le_successNumerator_of_half {r q : ℕ} (hr : 0 < r) {probability : ℝ}
    (hbound : probability ≤ (successNumerator q : ℝ) / (2 * (r : ℝ)))
    (hsuccess : (1 : ℝ) / 2 ≤ probability) : r ≤ successNumerator q := by
  have h := hsuccess.trans hbound
  rw [le_div_iff₀ (by positivity)] at h
  have h' : (r : ℝ) ≤ (successNumerator q : ℝ) := by linarith
  exact_mod_cast h'

theorem successNumerator_le_sq_add_two (q : ℕ) : successNumerator q ≤ (q + 3) ^ 2 + 2 := by
  unfold successNumerator
  rw [pow_two]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _

theorem sqrt_order_sub_two_le_budget {r q : ℕ} (h : r ≤ successNumerator q) :
    Real.sqrt ((r : ℝ) - 2) ≤ (q : ℝ) + 3 := by
  have hr : (r : ℝ) ≤ ((q : ℝ) + 3) ^ 2 + 2 := by
    exact_mod_cast h.trans (successNumerator_le_sq_add_two q)
  apply (Real.sqrt_le_left (by positivity)).mpr
  linarith

/-- The integer form gives `q + 2 ≥ t` when `r ≥ t²` and `t ≥ 3`. -/
theorem threshold_le_budget_add_two {r q t : ℕ} (ht : 3 ≤ t) (hr : t ^ 2 ≤ r)
    (hbudget : r ≤ successNumerator q) : t ≤ q + 2 := by
  by_contra! hlt
  have hprod : (q + 3) * (q + 2) ≤ t * (t - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hsquare : t ≤ t * t := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left t (show 1 ≤ t by omega)
  rw [Nat.mul_sub_left_distrib, Nat.mul_one] at hprod
  rw [pow_two] at hr
  unfold successNumerator at hbudget
  omega

end CryptoLean.GenericDLog
