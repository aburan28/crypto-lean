import Mathlib

/-!
# All-pairs shortest paths in truly subcubic time (ProofAtlas #221)

This module formalizes

* the **shortest-path distance** of a weighted digraph on `Fin n` with weights in
  `ℕ∞ = WithTop ℕ` (`⊤` = missing edge), as an infimum over walks;
* the **Floyd–Warshall algorithm** as an explicit straight-line program of in-place
  *relaxation* instructions `D[i][j] := min D[i][j] (D[i][k] + D[k][j])`, executed with an
  operation counter, together with the **known result** that it computes exact distances
  using exactly `n ^ 3` relaxation steps (Floyd 1962; Warshall 1962);
* a concrete **word-RAM** (uniform finite program, unit-cost `w`-bit word operations,
  indirect addressing, trans-dichotomous word size) with a fixed input/output encoding;
* the **open problem** #221 as an unproved `Prop` on that word-RAM (`APSPTrulySubcubic`) and
  its polynomially-bounded-weight variant.

## Modelling choices (stated honestly)

* Weights are non-negative integers (`ℕ`) plus `⊤` for missing edges. The ProofAtlas
  statement speaks of "weighted" graphs, which in the literature means arbitrary real (or
  integer) weights with no negative cycles. Non-negative integer APSP is subcubically
  equivalent to the general integer case (Fischer–Meyer 1971; Vassilevska Williams–Williams
  2010/2018), but that equivalence is **not** formalized. Negative and real weights are not
  modelled; in particular the real-weight case (real RAM) is not built, and
  `APSPSubcubicSchema` is only a model-parametric template, not a statement of #221.
* The machine is the word-RAM with instructions `+ − × div and or xor shl shr`, indirect
  load/store and `<`-jump, results mod `2^w`, word size `d·(log₂ n + log₂(B+1) + 1)` with the
  constant `d` chosen by the algorithm. In restricted (min,+) straight-line models Kerr-type
  `Ω(n³)` bounds are known, so `relaxModel` (which hosts the Floyd–Warshall bound) is not a
  faithful model for the question.
* Status note (neutral, not adjudicated): ProofAtlas records a resolution claim under review
  (Alman & Vassilevska Williams, `O(n^2.99942)` for polynomially bounded integer weights).
  Nothing here asserts or refutes it; the corresponding restricted `Prop` is
  `APSPTrulySubcubicPolyWeights c`.

The optional (min,+)-power reformulation (distances = `(n-1)`-th min-plus power of the
weight matrix) is not formalized here.
-/

namespace CryptoLean.OpenProblems.APSP

/-- A weighted digraph on `Fin n`: `W i j` is the weight of the edge `i → j`, `⊤` if absent. -/
abbrev Weights (n : ℕ) := Fin n → Fin n → ℕ∞

/-- Cost of the walk `i → v₁ → … → v_m → j` whose list of intermediate vertices is
`[v₁, …, v_m]` (the empty list is the single edge `i → j`). -/
def walkCost {n : ℕ} (W : Weights n) : Fin n → List (Fin n) → Fin n → ℕ∞
  | i, [], j => W i j
  | i, v :: l, j => W i v + walkCost W v l j

/-- Achievable costs of walks from `i` to `j` all of whose intermediate vertices lie in `S`,
including the empty (length-zero) walk of cost `0` when `i = j`. -/
def walkCosts {n : ℕ} (W : Weights n) (S : Set (Fin n)) (i j : Fin n) : Set ℕ∞ :=
  {c | (i = j ∧ c = 0) ∨ ∃ l : List (Fin n), (∀ v ∈ l, v ∈ S) ∧ c = walkCost W i l j}

/-- Shortest `i → j` distance using only intermediate vertices in `S` (`⊤` if none exists). -/
noncomputable def distVia {n : ℕ} (W : Weights n) (S : Set (Fin n)) (i j : Fin n) : ℕ∞ :=
  sInf (walkCosts W S i j)

/-- **Shortest-path distance**: infimum of the costs of all walks from `i` to `j`
(`0` for `i = j`, `⊤` if `j` is unreachable from `i`). -/
noncomputable def apspDist {n : ℕ} (W : Weights n) : Weights n := distVia W Set.univ

lemma walkCost_append_cons {n : ℕ} (W : Weights n) (i k j : Fin n) (m r : List (Fin n)) :
    walkCost W i (m ++ k :: r) j = walkCost W i m k + walkCost W k r j := by
  induction m generalizing i with
  | nil => rfl
  | cons v m ih => simp [walkCost, ih, add_assoc]

lemma distVia_le {n : ℕ} {W : Weights n} {S : Set (Fin n)} {i j : Fin n} {c : ℕ∞}
    (h : c ∈ walkCosts W S i j) : distVia W S i j ≤ c := sInf_le h

lemma distVia_mono {n : ℕ} (W : Weights n) {S T : Set (Fin n)} (h : S ⊆ T) (i j : Fin n) :
    distVia W T i j ≤ distVia W S i j := by
  apply sInf_le_sInf
  rintro c (hc | ⟨l, hl, rfl⟩)
  · exact Or.inl hc
  · exact Or.inr ⟨l, fun v hv => h (hl v hv), rfl⟩

/-- Walks into `k` through `insert k S` cost at least `distVia W S i k`. -/
lemma distVia_le_walk_to {n : ℕ} (W : Weights n) (S : Set (Fin n)) (i k : Fin n) :
    ∀ l : List (Fin n), (∀ v ∈ l, v ∈ insert k S) →
      distVia W S i k ≤ walkCost W i l k := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    intro hl
    by_cases hk : k ∈ l
    · obtain ⟨m, r, rfl⟩ := List.append_of_mem hk
      rw [walkCost_append_cons]
      refine le_trans ?_ le_self_add
      exact ih m.length (by simp at h; omega) m rfl
        (fun v hv => hl v (by simp [hv]))
    · apply distVia_le
      refine Or.inr ⟨l, fun v hv => ?_, rfl⟩
      rcases hl v hv with hv' | hv'
      · exact absurd (hv' ▸ hv) hk
      · exact hv'

/-- Walks out of `k` through `insert k S` cost at least `distVia W S k j`. -/
lemma distVia_le_walk_from {n : ℕ} (W : Weights n) (S : Set (Fin n)) (k j : Fin n) :
    ∀ l : List (Fin n), (∀ v ∈ l, v ∈ insert k S) →
      distVia W S k j ≤ walkCost W k l j := by
  intro l
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ N ih =>
    intro hl
    by_cases hk : k ∈ l
    · obtain ⟨m, r, rfl⟩ := List.append_of_mem hk
      rw [walkCost_append_cons]
      refine le_trans ?_ le_add_self
      exact ih r.length (by simp at h; omega) r rfl
        (fun v hv => hl v (by simp [hv]))
    · apply distVia_le
      refine Or.inr ⟨l, fun v hv => ?_, rfl⟩
      rcases hl v hv with hv' | hv'
      · exact absurd (hv' ▸ hv) hk
      · exact hv'

/-- The Floyd–Warshall recurrence: allowing one more intermediate vertex `k`. -/
theorem distVia_insert {n : ℕ} (W : Weights n) (S : Set (Fin n)) (k i j : Fin n) :
    distVia W (insert k S) i j =
      min (distVia W S i j) (distVia W S i k + distVia W S k j) := by
  apply le_antisymm
  · refine le_min (distVia_mono W (Set.subset_insert k S) i j) ?_
    -- upper bound by concatenating optimal walks (infima are attained in `ℕ∞`)
    by_cases h1 : (walkCosts W S i k).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at h1
      simp [distVia, h1]
    by_cases h2 : (walkCosts W S k j).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at h2
      simp [distVia, h2]
    have m1 := csInf_mem h1
    have m2 := csInf_mem h2
    change distVia W S i k ∈ _ at m1
    change distVia W S k j ∈ _ at m2
    rcases m1 with ⟨rfl, e1⟩ | ⟨l₁, hl₁, e1⟩
    · rw [e1, zero_add]; exact distVia_mono W (Set.subset_insert _ S) _ _
    rcases m2 with ⟨rfl, e2⟩ | ⟨l₂, hl₂, e2⟩
    · rw [e2, add_zero]; exact distVia_mono W (Set.subset_insert _ S) _ _
    rw [e1, e2, ← walkCost_append_cons]
    apply distVia_le
    refine Or.inr ⟨l₁ ++ k :: l₂, fun v hv => ?_, rfl⟩
    simp only [List.mem_append, List.mem_cons] at hv
    rcases hv with hv | hv | hv
    · exact Or.inr (hl₁ v hv)
    · exact Or.inl hv
    · exact Or.inr (hl₂ v hv)
  · apply le_sInf
    rintro c (⟨rfl, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact min_le_of_left_le (distVia_le (Or.inl ⟨rfl, rfl⟩))
    · by_cases hk : k ∈ l
      · obtain ⟨m, r, rfl⟩ := List.append_of_mem hk
        rw [walkCost_append_cons]
        refine min_le_of_right_le (add_le_add ?_ ?_)
        · exact distVia_le_walk_to W S i k m (fun v hv => hl v (by simp [hv]))
        · exact distVia_le_walk_from W S k j r (fun v hv => hl v (by simp [hv]))
      · refine min_le_of_left_le (distVia_le (Or.inr ⟨l, fun v hv => ?_, rfl⟩))
        rcases hl v hv with hv' | hv'
        · exact absurd (hv' ▸ hv) hk
        · exact hv'

/-- Initial matrix of Floyd–Warshall: `0` on the diagonal, the edge weight elsewhere. -/
def initMatrix {n : ℕ} (W : Weights n) : Weights n := fun i j => if i = j then 0 else W i j

theorem distVia_empty {n : ℕ} (W : Weights n) : distVia W ∅ = initMatrix W := by
  funext i j
  have hset : walkCosts W ∅ i j = {c | (i = j ∧ c = 0) ∨ c = W i j} := by
    ext c
    simp only [walkCosts, Set.mem_ofPred_eq, Set.mem_empty_iff_false, imp_false]
    constructor
    · rintro (h | ⟨l, hl, rfl⟩)
      · exact Or.inl h
      · cases l with
        | nil => exact Or.inr rfl
        | cons v l => exact absurd List.mem_cons_self (hl v)
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨[], by simp, rfl⟩
  unfold distVia initMatrix
  rw [hset]
  split_ifs with h
  · apply le_antisymm (sInf_le (Or.inl ⟨h, rfl⟩)) bot_le
  · have : {c : ℕ∞ | (i = j ∧ c = 0) ∨ c = W i j} = {W i j} := by
      ext c; simp [h]
    rw [this, sInf_singleton]

/-! ### Floyd–Warshall as a counted relaxation program -/

/-- A relaxation instruction `(i, j, k)`: `D[i][j] := min D[i][j] (D[i][k] + D[k][j])`. -/
abbrev Instr (n : ℕ) := Fin n × Fin n × Fin n

/-- Overwrite one entry of a matrix. -/
def setEntry {n : ℕ} (D : Weights n) (a b : Fin n) (v : ℕ∞) : Weights n :=
  fun i j => if i = a ∧ j = b then v else D i j

/-- Execute one relaxation instruction in place. -/
noncomputable def relax {n : ℕ} (D : Weights n) (ins : Instr n) : Weights n :=
  setEntry D ins.1 ins.2.1 (min (D ins.1 ins.2.1) (D ins.1 ins.2.2 + D ins.2.2 ins.2.1))

/-- Run a relaxation program, counting one step per (min,+) relaxation. -/
noncomputable def exec {n : ℕ} (P : List (Instr n)) (s : Weights n × ℕ) : Weights n × ℕ :=
  P.foldl (fun s ins => (relax s.1 ins, s.2 + 1)) s

lemma exec_eq {n : ℕ} (P : List (Instr n)) (D : Weights n) (c : ℕ) :
    exec P (D, c) = (P.foldl relax D, c + P.length) := by
  induction P generalizing D c with
  | nil => rfl
  | cons ins P ih =>
    simp only [exec, List.foldl_cons] at ih ⊢
    rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1]

/-- Round `k` of Floyd–Warshall: relax every pair `(i, j)` through `k`, row by row. -/
def fwRound (n : ℕ) (k : Fin n) : List (Instr n) :=
  (List.finRange n ×ˢ List.finRange n).map fun p => (p.1, p.2, k)

/-- The Floyd–Warshall program: rounds `k = 0, 1, …, n-1`. -/
def fwProg (n : ℕ) : List (Instr n) := (List.finRange n).flatMap (fwRound n)

/-- Floyd–Warshall: run `fwProg` on the initial matrix; returns distances and step count. -/
noncomputable def floydWarshall {n : ℕ} (W : Weights n) : Weights n × ℕ := exec (fwProg n) (initMatrix W, 0)

/-- One full round of in-place relaxations through `k` (in any order, over any list of
pairs) acts as the simultaneous update, because row/column `k` never changes. -/
lemma foldl_relax_pairs {n : ℕ} (D : Weights n) (k : Fin n) (L : List (Fin n × Fin n)) :
    (L.map fun p => (p.1, p.2, k)).foldl relax D =
      fun i j => if (i, j) ∈ L then min (D i j) (D i k + D k j) else D i j := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L p ih =>
    obtain ⟨a, b⟩ := p
    rw [List.map_append, List.foldl_append, ih]
    set R : Weights n := fun i j => if (i, j) ∈ L then min (D i j) (D i k + D k j) else D i j
    have hRak : R a k = D a k := by
      simp only [R]; split_ifs
      · exact min_eq_left le_self_add
      · rfl
    have hRkb : R k b = D k b := by
      simp only [R]; split_ifs
      · exact min_eq_left le_add_self
      · rfl
    funext i j
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, relax, setEntry,
      hRak, hRkb, List.mem_append, List.mem_singleton, Prod.mk.injEq]
    by_cases hij : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, ite_true, or_true]
      simp only [R]; split_ifs
      · rw [min_assoc, min_self]
      · rfl
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hij)]
      simp only [R, hij, or_false]

lemma foldl_fwRound {n : ℕ} (D : Weights n) (k : Fin n) :
    (fwRound n k).foldl relax D = fun i j => min (D i j) (D i k + D k j) := by
  rw [fwRound, foldl_relax_pairs]
  funext i j
  simp [List.mem_product]

lemma foldl_rounds {n : ℕ} (W : Weights n) (ks : List (Fin n)) (S : Set (Fin n)) :
    ks.foldl (fun D k => (fwRound n k).foldl relax D) (distVia W S) =
      distVia W (S ∪ {v | v ∈ ks}) := by
  induction ks generalizing S with
  | nil => simp
  | cons k ks ih =>
    rw [List.foldl_cons, foldl_fwRound]
    have : (fun i j => min (distVia W S i j) (distVia W S i k + distVia W S k j)) =
        distVia W (insert k S) := by
      funext i j; rw [distVia_insert]
    rw [this, ih]
    congr 1
    ext v; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_ofPred_eq, List.mem_cons]
    tauto

lemma length_fwProg (n : ℕ) : (fwProg n).length = n ^ 3 := by
  simp [fwProg, List.length_flatMap, fwRound, List.length_product, List.sum_replicate]
  ring

/-- **Floyd–Warshall** (Known result; R. W. Floyd, "Algorithm 97: Shortest path",
CACM 5(6), 1962; S. Warshall, J. ACM 9(1), 1962; see CLRS §25.2). On every non-negatively
weighted digraph with `n` vertices, the in-place Floyd–Warshall relaxation program outputs
the exact shortest-path distance matrix and performs exactly `n ^ 3` (min,+) relaxation
steps. -/
theorem floydWarshall_correct {n : ℕ} (W : Weights n) :
    (floydWarshall W).1 = apspDist W ∧ (floydWarshall W).2 = n ^ 3 := by
  rw [floydWarshall, exec_eq, fwProg, List.foldl_flatMap, ← distVia_empty, foldl_rounds]
  refine ⟨?_, ?_⟩
  · simp only [apspDist]
    congr 1
    ext v; simp
  · simpa [fwProg] using length_fwProg n

/-! ### A concrete word-RAM

The machine on which #221 is posed for integer weights is the (trans-dichotomous) word-RAM:
a single finite program (uniform in `n`), unit-cost instructions on `w`-bit words, indirect
addressing, and a word size `w` large enough to hold `n` and the weights. We build exactly
that machine here, so that the open-problem `Prop` below has a fixed meaning that cannot be
changed by choosing a cost model. -/

/-- Word-RAM instructions. Arguments `d a b s` are (direct) memory addresses, `k` a
constant, `t` a jump target. -/
inductive WInstr
  | const (d k : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | mul (d a b : ℕ)
  | div (d a b : ℕ)
  | land (d a b : ℕ)
  | lor (d a b : ℕ)
  | xor (d a b : ℕ)
  | shl (d a b : ℕ)
  | shr (d a b : ℕ)
  /-- indirect load `M[d] := M[M[a]]` -/
  | load (d a : ℕ)
  /-- indirect store `M[M[a]] := M[s]` -/
  | store (a s : ℕ)
  /-- conditional jump: `if M[a] < M[b] then goto t` -/
  | jlt (a b t : ℕ)
  deriving DecidableEq

/-- A word-RAM program: a finite instruction list. Execution halts when the program counter
leaves the list. -/
abbrev WProg := List WInstr

/-- Machine configuration: program counter and memory (address ↦ word). -/
structure WConfig where
  pc : ℕ
  mem : ℕ → ℕ

/-- Write `v` into memory cell `d`. -/
def WConfig.write (M : ℕ → ℕ) (d v : ℕ) : ℕ → ℕ := Function.update M d v

/-- Execute one instruction with word size `w` (all results reduced mod `2 ^ w`). -/
def execInstr (w : ℕ) (c : WConfig) : WInstr → WConfig
  | .const d k => ⟨c.pc + 1, WConfig.write c.mem d (k % 2 ^ w)⟩
  | .add d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a + c.mem b) % 2 ^ w)⟩
  | .sub d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a + 2 ^ w - c.mem b) % 2 ^ w)⟩
  | .mul d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a * c.mem b) % 2 ^ w)⟩
  | .div d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a / c.mem b) % 2 ^ w)⟩
  | .land d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a &&& c.mem b) % 2 ^ w)⟩
  | .lor d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a ||| c.mem b) % 2 ^ w)⟩
  | .xor d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a ^^^ c.mem b) % 2 ^ w)⟩
  | .shl d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a <<< c.mem b) % 2 ^ w)⟩
  | .shr d a b => ⟨c.pc + 1, WConfig.write c.mem d ((c.mem a >>> c.mem b) % 2 ^ w)⟩
  | .load d a => ⟨c.pc + 1, WConfig.write c.mem d (c.mem (c.mem a) % 2 ^ w)⟩
  | .store a s => ⟨c.pc + 1, WConfig.write c.mem (c.mem a) (c.mem s % 2 ^ w)⟩
  | .jlt a b t => ⟨if c.mem a < c.mem b then t else c.pc + 1, c.mem⟩

/-- A configuration is halted when the program counter is outside the program. -/
def WHalted (P : WProg) (c : WConfig) : Prop := P.length ≤ c.pc

/-- One unit-cost step (a halted configuration stays put). -/
def wstep (w : ℕ) (P : WProg) (c : WConfig) : WConfig :=
  match P[c.pc]? with
  | some i => execInstr w c i
  | none => c

/-- The configuration after `t` steps. -/
def wrun (w : ℕ) (P : WProg) (c : WConfig) : ℕ → WConfig
  | 0 => c
  | t + 1 => wrun w P (wstep w P c) t

/-- Address of the "edge present" flag of entry `(i, j)` (input and output). -/
def flagAddr (n : ℕ) (i j : Fin n) : ℕ := 1 + 2 * (i.val * n + j.val)

/-- Address of the weight / distance value of entry `(i, j)` (input and output). -/
def valAddr (n : ℕ) (i j : Fin n) : ℕ := 2 + 2 * (i.val * n + j.val)

/-- Largest finite edge weight (`0` if there is none). -/
def maxWeight {n : ℕ} (W : Weights n) : ℕ :=
  Finset.univ.sup fun p : Fin n × Fin n => (W p.1 p.2).toNat

/-- Trans-dichotomous word size with constant `d`: `d · (log₂ n + log₂ (B + 1) + 1)` bits,
where `B` is the largest weight. -/
def wordSize (d : ℕ) {n : ℕ} (W : Weights n) : ℕ :=
  d * (Nat.log 2 n + Nat.log 2 (maxWeight W + 1) + 1)

/-- Initial memory: `M[0] = n`, and for every pair `(i, j)` the flag cell holds `1` if the
edge `i → j` is present (`0` if `W i j = ⊤`) and the value cell holds its weight; all other
cells are `0`. Every cell is reduced mod `2 ^ w`. -/
def inputMem (w n : ℕ) (W : Weights n) : ℕ → ℕ := fun a =>
  if a = 0 then n % 2 ^ w else
  if h : (a - 1) / 2 < n * n then
    have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    let i : Fin n := ⟨(a - 1) / 2 / n, Nat.div_lt_of_lt_mul h⟩
    let j : Fin n := ⟨(a - 1) / 2 % n, Nat.mod_lt _ hn⟩
    if (a - 1) % 2 = 0 then (if W i j = ⊤ then 0 else 1 % 2 ^ w)
    else (W i j).toNat % 2 ^ w
  else 0

/-- Output decoding: entry `(i, j)` is `⊤` if its flag cell is `0`, otherwise the value
cell. -/
def decodeOut (n : ℕ) (M : ℕ → ℕ) : Weights n := fun i j =>
  if M (flagAddr n i j) = 0 then ⊤ else (M (valAddr n i j) : ℕ∞)

lemma addr_index {n : ℕ} (i j : Fin n) :
    (i.val * n + j.val) / n = i.val ∧ (i.val * n + j.val) % n = j.val ∧
      i.val * n + j.val < n * n := by
  have hn : 0 < n := Fin.pos i
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  · calc i.val * n + j.val < i.val * n + n := by have := j.isLt; omega
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ i.isLt

/-- Sanity check of the encoding (non-vacuity of the model): with a word size of at least one
bit that holds every weight, decoding the input memory gives back the weight matrix. -/
theorem decodeOut_inputMem {w n : ℕ} (W : Weights n) (hw : 1 ≤ w)
    (hW : ∀ i j, (W i j).toNat < 2 ^ w) : decodeOut n (inputMem w n W) = W := by
  funext i j
  obtain ⟨h1, h2, h3⟩ := addr_index i j
  have h1w : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
  have hf : (flagAddr n i j - 1) / 2 = i.val * n + j.val := by unfold flagAddr; omega
  have hv : (valAddr n i j - 1) / 2 = i.val * n + j.val := by unfold valAddr; omega
  have hf2 : (flagAddr n i j - 1) % 2 = 0 := by unfold flagAddr; omega
  have hv2 : (valAddr n i j - 1) % 2 ≠ 0 := by unfold valAddr; omega
  have hf0 : flagAddr n i j ≠ 0 := by unfold flagAddr; omega
  have hv0 : valAddr n i j ≠ 0 := by unfold valAddr; omega
  have eI : (⟨(i.val * n + j.val) / n, by rw [h1]; exact i.isLt⟩ : Fin n) = i := Fin.ext h1
  have eJ : (⟨(i.val * n + j.val) % n, by rw [h2]; exact j.isLt⟩ : Fin n) = j := Fin.ext h2
  simp only [decodeOut, inputMem, hf0, hv0, ite_false, hf, hv, h3, dite_eq_left, hf2, hv2,
    ite_true, eI, eJ, h1w]
  by_cases hT : W i j = ⊤
  · simp [hT]
  · simp only [hT, ite_false, one_ne_zero, Nat.mod_eq_of_lt (hW i j)]
    exact ENat.natCast_toNat hT

/-- Program `P` solves APSP on `W` within `t` steps with word size `w`: started from the
encoded input at `pc = 0`, after `t` unit-cost steps the machine has halted and the output
cells decode to the exact distance matrix. -/
def WSolvesWithin (P : WProg) (w : ℕ) {n : ℕ} (W : Weights n) (t : ℕ) : Prop :=
  let c := wrun w P ⟨0, inputMem w n W⟩ t
  WHalted P c ∧ decodeOut n c.mem = apspDist W

/-- Truly subcubic APSP on the word-RAM for the admissible inputs `Adm`: a fixed `ε > 0`, a
word-size constant `d`, a single program `P` and constants `C, N` such that on every
admissible `n`-vertex input `P` halts with the exact distances, within `C · n^(3-ε)` steps
once `n ≥ N`. -/
def WordRAMSubcubic (Adm : ∀ n, Weights n → Prop) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ d : ℕ, ∃ P : WProg, ∃ C : ℝ, ∃ N : ℕ,
    ∀ n (W : Weights n), Adm n W → ∃ t, WSolvesWithin P (wordSize d W) W t ∧
      (N ≤ n → (t : ℝ) ≤ C * (n : ℝ) ^ (3 - ε))

/-- Edge weights polynomially bounded: every present edge has weight at most `n ^ c`. -/
def PolyBoundedWeights (c : ℕ) : ∀ n, Weights n → Prop :=
  fun n W => ∀ i j, W i j = ⊤ ∨ W i j ≤ (n : ℕ∞) ^ c

/-- **Open problem (ProofAtlas #221, edition 2026-11-12): All-Pairs Shortest Paths in Truly
Subcubic Time.** Exact statement: "Determine whether exact all-pairs shortest paths on
weighted n-vertex graphs can be computed in O(n^(3-epsilon)) time for some fixed epsilon
greater than zero."

This `Prop` is the positive answer on the concrete word-RAM built above, for all
non-negative integer weights. It is NOT proved here and NOT claimed true or false.
Modelling simplifications:
* Machine: unit-cost word-RAM with one uniform finite program, instructions
  `+ − × div and or xor shl shr`, indirect load/store and `<`-jump, all mod `2^w`; word size
  `w = d·(log₂ n + log₂(B+1) + 1)` with `d` chosen by the algorithm (`B` = largest weight),
  i.e. the standard trans-dichotomous convention that a word holds `n` and any weight.
  Input layout, `⊤` encoding by a flag cell, and in-place output are fixed conventions of
  this file. Variants of the instruction set (e.g. without multiplication) are not covered.
* Weights are non-negative integers plus `⊤` (no edge). Negative integer weights (no
  negative cycles) and real weights are NOT modelled; they are subcubically equivalent to
  the non-negative case in the literature (Fischer–Meyer 1971; Vassilevska Williams–Williams
  2010/2018) but that is not formalized. The real-weight question lives on the real RAM,
  which is not built here; `APSPSubcubicSchema` is only a model-parametric template for it.
* Correctness is required on all inputs; the time bound for `n ≥ N`.

ProofAtlas lists a resolution claim under review (Alman & Vassilevska Williams,
`O(n^2.99942)` for polynomially bounded integer weights, cf. `APSPTrulySubcubicPolyWeights`);
this file neither asserts nor refutes it. -/
def APSPTrulySubcubic : Prop := WordRAMSubcubic fun _ _ => True

/-- Variant of #221 restricted to weights at most `n ^ c` (the setting of the pending
resolution claim, neither asserted nor refuted here), on the same word-RAM. Same caveats as
`APSPTrulySubcubic`; note the word size is then `O(log n)`. -/
def APSPTrulySubcubicPolyWeights (c : ℕ) : Prop := WordRAMSubcubic (PolyBoundedWeights c)

/-- The unrestricted version implies every polynomially-bounded-weight version (monotonicity
in the admissible input class). -/
theorem APSPTrulySubcubic.polyWeights (h : APSPTrulySubcubic) (c : ℕ) :
    APSPTrulySubcubicPolyWeights c := by
  obtain ⟨ε, hε, d, P, C, N, hP⟩ := h
  exact ⟨ε, hε, d, P, C, N, fun n W _ => hP n W trivial⟩

/-! ### Model-parametric schema (not the problem statement)

`CostModel` is an arbitrary type of programs with a semantics returning an output matrix and
a step count; nothing constrains how steps are counted, so `APSPSubcubicSchema M` can be made
true (a model that counts nothing) or false (an empty model) by choosing `M`. It is a
template only, kept to host the Floyd–Warshall bound in the relaxation model and to indicate
the shape of a real-RAM version, which is not built here. It is NOT a statement of #221. -/

/-- An abstract counted-operation model: programs (an arbitrary type — no uniformity is
imposed) mapping an input matrix of any size to an output matrix and a step count. -/
structure CostModel where
  /-- Programs. -/
  Prog : Type
  /-- Semantics: output matrix and number of steps charged. -/
  run : Prog → ∀ {n : ℕ}, Weights n → Weights n × ℕ

/-- Program `p` of model `M` computes APSP exactly on all admissible inputs, within
`O(T n)` steps. -/
def ComputesAPSPWithin (M : CostModel) (Adm : ∀ n, Weights n → Prop) (p : M.Prog)
    (T : ℕ → ℝ) : Prop :=
  (∀ n (W : Weights n), Adm n W → (M.run p W).1 = apspDist W) ∧
    ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ W : Weights n, Adm n W → ((M.run p W).2 : ℝ) ≤ C * T n

/-- Schema only (see section comment): truly subcubic APSP in an arbitrary model `M`. -/
def APSPSubcubicSchema (M : CostModel) (Adm : ∀ n, Weights n → Prop) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ p : M.Prog, ComputesAPSPWithin M Adm p (fun n => (n : ℝ) ^ (3 - ε))

/-- The oblivious relaxation-program model: a program is an arbitrary (non-uniform) family
`n ↦` list of relaxation instructions, run on the initial matrix and charged one step per
relaxation. Not a faithful instance for #221 (Kerr-type cubic lower bounds hold for such
(min,+) straight-line programs); it hosts the Floyd–Warshall bound. -/
noncomputable def relaxModel : CostModel where
  Prog := ∀ n, List (Instr n)
  run p := fun {n} W => exec (p n) (initMatrix W, 0)

/-- **Cubic APSP** (Known result; Floyd 1962, Warshall 1962): in the relaxation model,
Floyd–Warshall computes exact APSP on all inputs within `n ^ 3` steps. -/
theorem relaxModel_cubic :
    ComputesAPSPWithin relaxModel (fun _ _ => True) fwProg (fun n => (n : ℝ) ^ (3 : ℝ)) := by
  refine ⟨fun n W _ => (floydWarshall_correct W).1, 1, 0, fun n _ W _ => ?_⟩
  have h := (floydWarshall_correct W).2
  change ((floydWarshall W).2 : ℝ) ≤ _
  rw [h, one_mul]
  show ((n ^ 3 : ℕ) : ℝ) ≤ (n : ℝ) ^ (3 : ℝ)
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast; exact le_rfl

end CryptoLean.OpenProblems.APSP

#print axioms CryptoLean.OpenProblems.APSP.distVia_insert
#print axioms CryptoLean.OpenProblems.APSP.floydWarshall_correct
#print axioms CryptoLean.OpenProblems.APSP.relaxModel_cubic
#print axioms CryptoLean.OpenProblems.APSP.APSPTrulySubcubic.polyWeights
#print axioms CryptoLean.OpenProblems.APSP.decodeOut_inputMem
