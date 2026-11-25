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

/-- Keep the strategy's own guess if it finishes within the cutoff. -/
def Strategy.truncate {r : ℕ} {View : ℕ → Type*} {n q : ℕ} (fallback : ZMod r)
    (strategy : Strategy r View n q) (cutoff : ℕ) : Strategy r View n cutoff :=
  match strategy, cutoff with
  | .finish guess, _ => .finish guess
  | .query _ _, 0 => .finish fun _ => fallback
  | .query choose next, cutoff + 1 =>
    .query choose fun view => (next view).truncate fallback cutoff
termination_by cutoff

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

theorem run_size_ge {r : ℕ} {V : Type*} [DecidableEq V] {View : ℕ → Type*}
    (observe : ∀ n, Pattern n → View n) (oracle : Oracle r V) {n q : ℕ}
    (strategy : Strategy r View n q) (table : Fin n → V) :
    n ≤ (run observe oracle strategy table).size := by
  induction q generalizing n with
  | zero => cases strategy; simp [run]
  | succ q ih =>
    cases strategy with
    | finish => simp [run]
    | query choose next =>
      rw [run]
      exact (Nat.le_succ n).trans (ih _ _)

/-- Truncation preserves the whole execution whenever its actual query count fits. -/
theorem run_truncate_eq_of_size_le {r : ℕ} {V : Type*} [DecidableEq V] {View : ℕ → Type*}
    (observe : ∀ n, Pattern n → View n) (oracle : Oracle r V) {n q cutoff : ℕ}
    (strategy : Strategy r View n q) (table : Fin n → V) (fallback : ZMod r)
    (hsize : (run observe oracle strategy table).size ≤ n + cutoff) :
    run observe oracle (strategy.truncate fallback cutoff) table = run observe oracle strategy table := by
  induction q generalizing n cutoff with
  | zero => cases strategy; simp [Strategy.truncate, run]
  | succ q ih =>
    cases strategy with
    | finish => simp [Strategy.truncate, run]
    | query choose next =>
      let view := observe n (equalityPattern table)
      let extended : Fin (n + 1) → V := Fin.snoc table (oracle n (choose view) table)
      have hsize' : (run observe oracle (next view) extended).size ≤ n + cutoff := by
        simpa only [run] using hsize
      cases cutoff with
      | zero =>
        have hmin := run_size_ge observe oracle (next view) extended
        omega
      | succ cutoff =>
        simp only [Strategy.truncate, run]
        exact ih _ _ (by simpa only [Nat.succ_add, Nat.add_succ] using hsize')

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

/-- An injective oracle map preserves both the stopping time and the guess. -/
theorem run_size_answer_eq_of_injOn {r : ℕ} {A B : Type*} [DecidableEq A] [DecidableEq B]
    {View : ℕ → Type*} (observe : ∀ n, Pattern n → View n) (oracleA : Oracle r A)
    (oracleB : Oracle r B) (f : A → B)
    (hmap : ∀ n cmd (table : Fin n → A), f (oracleA n cmd table) = oracleB n cmd (f ∘ table))
    {n q : ℕ} (strategy : Strategy r View n q) (table : Fin n → A)
    (hinj : Set.InjOn f (Set.range (run observe oracleA strategy table).table)) :
    ((run observe oracleB strategy (f ∘ table)).size, (run observe oracleB strategy (f ∘ table)).answer) =
      ((run observe oracleA strategy table).size, (run observe oracleA strategy table).answer) := by
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
      rw [htable]
      exact ih _ _ hinj

/-- If observations are preserved on the final table, the algorithm returns the same guess. -/
theorem run_answer_eq_of_injOn {r : ℕ} {A B : Type*} [DecidableEq A] [DecidableEq B]
    {View : ℕ → Type*} (observe : ∀ n, Pattern n → View n) (oracleA : Oracle r A)
    (oracleB : Oracle r B) (f : A → B)
    (hmap : ∀ n cmd (table : Fin n → A), f (oracleA n cmd table) = oracleB n cmd (f ∘ table))
    {n q : ℕ} (strategy : Strategy r View n q) (table : Fin n → A)
    (hinj : Set.InjOn f (Set.range (run observe oracleA strategy table).table)) :
    (run observe oracleB strategy (f ∘ table)).answer = (run observe oracleA strategy table).answer :=
  congrArg Prod.snd (run_size_answer_eq_of_injOn observe oracleA oracleB f hmap strategy table hinj)

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

/-- Every oracle call appends one handle to the three starting handles. -/
def scalarQueryCount (strategy : Strategy r View 3 q) (x : ZMod r) : ℕ :=
  (run observe (scalarOracle r samples) strategy (eval x ∘ startingForms r)).size - 3

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

/-- Turn a family of cutoff bounds into a mean query lower bound at positive success. -/
theorem sqrt_success_mul_order_div_two_le_of_cutoffs {r : ℕ} (hr : 0 < r)
    {success mean : ℝ} (hsuccess : 0 < success) (hmean : 0 ≤ mean)
    (hbound : ∀ cutoff : ℕ, success ≤ (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
      mean / ((cutoff : ℝ) + 1)) :
    Real.sqrt (success * (r : ℝ) / 2) ≤ 2 * mean / success + 2 := by
  let cutoff := ⌊2 * mean / success⌋₊
  have hcutoff : (cutoff : ℝ) ≤ 2 * mean / success := Nat.floor_le (by positivity)
  have htail : mean / ((cutoff : ℝ) + 1) < success / 2 := by
    have hf : 2 * mean / success < (cutoff : ℝ) + 1 := Nat.lt_floor_add_one _
    exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith only [(div_lt_iff₀ hsuccess).mp hf])
  have hcollision : success / 2 < (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) := by
    linarith only [hbound cutoff, htail]
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  have horder : success * (r : ℝ) ≤ (successNumerator cutoff : ℝ) := by
    nlinarith only [(lt_div_iff₀ (mul_pos two_pos hrReal)).mp hcollision]
  have hnum : (successNumerator cutoff : ℝ) = ((cutoff : ℝ) + 3) * ((cutoff : ℝ) + 2) + 2 := by
    simp [successNumerator]
  have hsquare : success * (r : ℝ) / 2 ≤ ((cutoff : ℝ) + 2) ^ 2 := by
    nlinarith only [horder, hnum, sq_nonneg (cutoff : ℝ), Nat.cast_nonneg (α := ℝ) cutoff]
  exact ((Real.sqrt_le_left (by positivity)).mpr hsquare).trans (add_le_add hcutoff le_rfl)

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

/-- Average a query count over the uniform secret. -/
noncomputable def expectedQueries (count : ZMod r → ℕ) : ℝ := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  exact (∑ x : ZMod r, (count x : ℝ)) / r

/-- Charge each solved scalar to the truncated run, a long run, or the supplied exceptional set. -/
theorem card_div_le_of_truncation (observe : ∀ n, Pattern n → View n)
    (samples : ℕ → ZMod r) (strategy : Strategy r View 3 q) (cutoff : ℕ)
    (solved exceptional : Finset (ZMod r)) (count : ZMod r → ℕ)
    (hcert : ∀ x ∈ solved, x ∉ exceptional → scalarGuess observe samples strategy x = x ∧
      scalarQueryCount observe samples strategy x ≤ count x) :
    (solved.card : ℝ) / r ≤ (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
      expectedQueries count / ((cutoff : ℝ) + 1) + (exceptional.card : ℝ) / r := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  let truncated := strategy.truncate 0 cutoff
  let long := (univ : Finset (ZMod r)).filter fun x => cutoff < count x
  have hsub : solved ⊆ (successSecrets observe samples truncated ∪ long) ∪ exceptional := by
    intro x hx
    apply Finset.mem_union.mpr
    by_cases hbad : x ∈ exceptional
    · exact Or.inr hbad
    left
    obtain ⟨hcorrect, hcount⟩ := hcert x hx hbad
    by_cases hlong : cutoff < count x
    · exact Finset.mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ _, hlong⟩))
    · apply Finset.mem_union.mpr
      left
      have hsize : (run observe (scalarOracle r samples) strategy (eval x ∘ startingForms r)).size ≤
          3 + cutoff := by
        unfold scalarQueryCount at hcount
        omega
      have hguess : scalarGuess observe samples truncated x = scalarGuess observe samples strategy x :=
        congrArg Execution.answer (run_truncate_eq_of_size_le observe (scalarOracle r samples)
          strategy (eval x ∘ startingForms r) 0 hsize)
      exact mem_filter.mpr ⟨mem_univ _, hguess.trans hcorrect⟩
  have hcard : solved.card ≤ (successSecrets observe samples truncated).card + long.card + exceptional.card :=
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _)).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hcost : long.card * (cutoff + 1) ≤ ∑ x : ZMod r, count x := by
    calc
      _ = ∑ _x ∈ long, (cutoff + 1) := by simp
      _ ≤ ∑ x ∈ long, count x :=
        Finset.sum_le_sum fun x hx => Nat.succ_le_of_lt (mem_filter.mp hx).2
      _ ≤ _ := Finset.sum_le_sum_of_subset (filter_subset ..)
  have hr : 0 < (r : ℝ) := by exact_mod_cast (Fact.out : r.Prime).pos
  have htail : (long.card : ℝ) / r ≤ expectedQueries count / ((cutoff : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    rw [div_mul_eq_mul_div₀, expectedQueries]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcost) hr.le
  have hsuccess : (solved.card : ℝ) / r ≤
      successProbability observe samples truncated + (long.card : ℝ) / r + (exceptional.card : ℝ) / r := by
    unfold successProbability
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hr.le
  exact hsuccess.trans (add_le_add (add_le_add (successProbability_le observe samples truncated) htail) le_rfl)

/-- A successful generic run either finishes within the cutoff or pays for at least one more call. -/
theorem successProbability_le_of_expectedQueries (observe : ∀ n, Pattern n → View n)
    (samples : ℕ → ZMod r) (strategy : Strategy r View 3 q) (cutoff : ℕ) :
    successProbability observe samples strategy ≤ (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
      expectedQueries (scalarQueryCount observe samples strategy) / ((cutoff : ℝ) + 1) := by
  simpa [successProbability] using card_div_le_of_truncation observe samples strategy cutoff
    (successSecrets observe samples strategy) ∅ (scalarQueryCount observe samples strategy)
    (fun _ hx _ => ⟨(mem_filter.mp hx).2, le_rfl⟩)

/-- Average the truncation bound over seeds that are independent of the uniform scalar. -/
theorem mixed_card_div_le_of_truncation {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) (cutoff : ℕ)
    (solved exceptional : Seed → Finset (ZMod r)) (count : Seed → ZMod r → ℕ)
    (exceptionBound : Seed → ℕ) (hbound : ∀ s, (exceptional s).card ≤ exceptionBound s)
    (hcert : ∀ s x, x ∈ solved s → x ∉ exceptional s → scalarGuess (observe s) (samples s) (strategy s) x = x ∧
      scalarQueryCount (observe s) (samples s) (strategy s) x ≤ count s x) :
    (∑ s, weights s * ((solved s).card : ℝ)) / (r : ℝ) ≤
      (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
        (∑ s, weights s * expectedQueries (count s)) / ((cutoff : ℝ) + 1) +
        (∑ s, weights s * (exceptionBound s : ℝ)) / (r : ℝ) := by
  have hr : 0 ≤ (r : ℝ) := by positivity
  calc
    _ = ∑ s, weights s * (((solved s).card : ℝ) / (r : ℝ)) := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    _ ≤ ∑ s, weights s * ((successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
        expectedQueries (count s) / ((cutoff : ℝ) + 1) + (exceptionBound s : ℝ) / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (hnonneg s)
      have hb : ((exceptional s).card : ℝ) ≤ (exceptionBound s : ℝ) := by exact_mod_cast hbound s
      exact (card_div_le_of_truncation (observe s) (samples s) (strategy s) cutoff
        (solved s) (exceptional s) (count s) (hcert s)).trans
        (add_le_add le_rfl (div_le_div_of_nonneg_right hb hr))
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hnorm, one_mul]
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- Average the actual query count over seeds independent of the uniform secret. -/
noncomputable def mixedExpectedQueries {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) : ℝ :=
  ∑ s, weights s * expectedQueries (scalarQueryCount (observe s) (samples s) (strategy s))

/-- A bound at every cutoff, expressed in terms of the mean of the actual query count. -/
theorem mixedSuccessProbability_le_of_expectedQueries {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q) (cutoff : ℕ) :
    mixedSuccessProbability weights observe samples strategy ≤ (successNumerator cutoff : ℝ) / (2 * (r : ℝ)) +
      mixedExpectedQueries weights observe samples strategy / ((cutoff : ℝ) + 1) := by
  simpa [mixedSuccessProbability, successProbability, mixedExpectedQueries, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    using mixed_card_div_le_of_truncation weights hnonneg hnorm observe samples strategy cutoff
      (fun s => successSecrets (observe s) (samples s) (strategy s)) (fun _ => ∅)
      (fun s => scalarQueryCount (observe s) (samples s) (strategy s)) (fun _ => 0)
      (fun _ => by simp) (fun _ _ hx _ => ⟨(mem_filter.mp hx).2, le_rfl⟩)

/-- Half success requires a mean query count of at least `sqrt r / 8 - 1 / 2`. -/
theorem sqrt_order_le_of_half_success_with_expectedQueries {Seed : Type*} [Fintype Seed] (weights : Seed → ℝ)
    (hnonneg : ∀ s, 0 ≤ weights s) (hnorm : ∑ s, weights s = 1)
    (observe : Seed → ∀ n, Pattern n → View n) (samples : Seed → ℕ → ZMod r)
    (strategy : Seed → Strategy r View 3 q)
    (hsuccess : (1 : ℝ) / 2 ≤ mixedSuccessProbability weights observe samples strategy) :
    Real.sqrt r ≤ 8 * mixedExpectedQueries weights observe samples strategy + 4 := by
  let mean := mixedExpectedQueries weights observe samples strategy
  have hmean : 0 ≤ mean := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hnonneg s) (by unfold expectedQueries; positivity)
  have h := sqrt_success_mul_order_div_two_le_of_cutoffs (Fact.out : r.Prime).pos
    (success := (1 : ℝ) / 2) (mean := mean) (by norm_num) hmean (fun cutoff =>
      hsuccess.trans (mixedSuccessProbability_le_of_expectedQueries weights hnonneg hnorm observe samples strategy cutoff))
  have hscale : (1 : ℝ) / 2 * (r : ℝ) / 2 = (r : ℝ) / 4 := by ring
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hscale, Real.sqrt_div (by positivity : (0 : ℝ) ≤ r), hsqrt] at h
  norm_num at h
  linarith only [h]

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
