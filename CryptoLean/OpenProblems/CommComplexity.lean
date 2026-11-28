import Mathlib

/-!
# Deterministic communication complexity and the Log-Rank Conjecture

Open problem (ProofAtlas list):
* #7 Log-Rank Conjecture (Lovász–Saks 1988) -> `LogRankConjecture` (OPEN, `def ... : Prop`).

The conjecture is **not** resolved here. What is proved are the two classical, known bounds that
sandwich deterministic communication complexity `D(f)` between `log₂ rank M_f` and `rank M_f + 1`:

* `rank_le_two_pow_detCC` / `clog_rank_le_detCC` (known result, Mehlhorn–Schmidt 1982):
  `rank M_f ≤ 2 ^ D(f)`, hence `⌈log₂ rank M_f⌉ ≤ D(f)`;
* `detCC_le_rank_add_one` (known result, folklore; Kushilevitz–Nisan, *Communication
  Complexity*, 1997, Ch. 1–2; Lovász 1990): `D(f) ≤ rank M_f + 1`.

The conjecture asks whether the exponential gap between these two bounds can be closed down to a
polynomial in `log rank`.

## Model

* A deterministic two-party protocol (`Protocol X Y`) is a binary tree: each internal node is
  owned by Alice (it branches on a bit `s x` computed from her input `x : X`) or by Bob (bit
  `s y` from `y : Y`); each leaf is labelled with the output bit. The cost of a protocol is its
  depth (worst-case number of bits exchanged), as in Kushilevitz–Nisan, Def. 1.1–1.2.
* `detCC f` is the minimum depth of a protocol computing `f : X → Y → Bool` exactly on all
  inputs, for finite `X`, `Y`.
* `boolMatrix f` is the 0/1 communication matrix `M_f x y = if f x y then 1 else 0` over `ℝ`,
  and its rank is Mathlib's `Matrix.rank`.
-/

namespace CryptoLean.OpenProblems.CommComplexity

open Matrix

universe u v

/-- A deterministic two-party communication protocol for inputs `x : X` (Alice) and `y : Y`
(Bob): a binary tree whose internal nodes are owned by Alice or Bob and branch on a bit that
the owner computes from her/his own input; leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf (b : Bool) : Protocol X Y
  | alice (s : X → Bool) (p₁ p₀ : Protocol X Y) : Protocol X Y
  | bob (s : Y → Bool) (p₁ p₀ : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on inputs `x, y` (follow the branch `p₁` when the sent bit is
`true`, `p₀` otherwise). -/
def eval : Protocol X Y → X → Y → Bool
  | leaf b, _, _ => b
  | alice s p₁ p₀, x, y => if s x then p₁.eval x y else p₀.eval x y
  | bob s p₁ p₀, x, y => if s y then p₁.eval x y else p₀.eval x y

/-- The cost of a protocol: the depth of the tree, i.e. the worst-case number of bits sent. -/
def depth : Protocol X Y → ℕ
  | leaf _ => 0
  | alice _ p₁ p₀ => max p₁.depth p₀.depth + 1
  | bob _ p₁ p₀ => max p₁.depth p₀.depth + 1

/-- `P` computes `f` exactly on every input pair. -/
def Computes (P : Protocol X Y) (f : X → Y → Bool) : Prop :=
  ∀ x y, P.eval x y = f x y

/-- Alice sends the `n` bits `g x`, one per round; then Bob announces `h (g x) y`. -/
def sendThenBob : (n : ℕ) → (X → Fin n → Bool) → ((Fin n → Bool) → Y → Bool) → Protocol X Y
  | 0, _, h => bob (fun y => h Fin.elim0 y) (leaf true) (leaf false)
  | n + 1, g, h =>
      alice (fun x => g x 0)
        (sendThenBob n (fun x i => g x i.succ) (fun w => h (Fin.cons true w)))
        (sendThenBob n (fun x i => g x i.succ) (fun w => h (Fin.cons false w)))

theorem eval_sendThenBob (n : ℕ) (g : X → Fin n → Bool) (h : (Fin n → Bool) → Y → Bool)
    (x : X) (y : Y) : (sendThenBob n g h).eval x y = h (g x) y := by
  induction n with
  | zero =>
    have hg : g x = Fin.elim0 := funext fun i => i.elim0
    simp only [sendThenBob, eval, hg]
    cases h Fin.elim0 y <;> rfl
  | succ n ih =>
    simp only [sendThenBob, eval, ih]
    cases hg : g x 0
    · simp only [Bool.false_eq_true, ite_false]
      congr 1
      rw [← hg]
      exact Fin.cons_self_tail (g x)
    · simp only [ite_true]
      congr 1
      rw [← hg]
      exact Fin.cons_self_tail (g x)

theorem depth_sendThenBob (n : ℕ) (g : X → Fin n → Bool) (h : (Fin n → Bool) → Y → Bool) :
    (sendThenBob n g h).depth = n + 1 := by
  induction n with
  | zero => simp [sendThenBob, depth]
  | succ n ih => simp [sendThenBob, depth, ih]

end Protocol

open Protocol

variable {X : Type u} {Y : Type v}

/-- The 0/1 communication matrix `M_f` of `f`, over `ℝ`. -/
def boolMatrix (f : X → Y → Bool) : Matrix X Y ℝ :=
  fun x y => if f x y then 1 else 0

/-- Subadditivity of matrix rank (over `ℝ`). -/
theorem rank_add_le' {m : Type*} {n : Type*} [Fintype n] (A B : Matrix m n ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℝ (A.mulVecLin + B.mulVecLin).range
      ≤ Module.finrank ℝ ↥(A.mulVecLin.range ⊔ B.mulVecLin.range) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

private theorem two_pow_add_le (a b : ℕ) : 2 ^ a + 2 ^ b ≤ 2 ^ (max a b + 1) := by
  have h1 : 2 ^ a ≤ 2 ^ max a b := Nat.pow_le_pow_right (by norm_num) (le_max_left a b)
  have h2 : 2 ^ b ≤ 2 ^ max a b := Nat.pow_le_pow_right (by norm_num) (le_max_right a b)
  rw [pow_succ]; omega

/-- **Known result** (rectangle / rank bound, Mehlhorn–Schmidt 1982; Kushilevitz–Nisan,
*Communication Complexity*, Lemma 1.28): the communication matrix of a protocol of depth `d`
is a sum of at most `2 ^ d` rank-one (monochromatic rectangle) matrices, so its rank is
at most `2 ^ d`. -/
theorem rank_boolMatrix_eval_le [Fintype X] [Fintype Y] (P : Protocol X Y) :
    (boolMatrix P.eval).rank ≤ 2 ^ P.depth := by
  classical
  induction P with
  | leaf b =>
    cases b
    · have : boolMatrix (Protocol.leaf false : Protocol X Y).eval = 0 := by
        ext x y; simp [boolMatrix, eval]
      simp [this, depth]
    · have : boolMatrix (Protocol.leaf true : Protocol X Y).eval
          = vecMulVec (fun _ => (1 : ℝ)) (fun _ => 1) := by
        ext x y; simp [boolMatrix, eval, vecMulVec]
      simpa [this, depth] using rank_vecMulVec_le (R := ℝ) (fun _ : X => (1 : ℝ)) (fun _ : Y => 1)
  | alice s p₁ p₀ ih₁ ih₀ =>
    have hdec : boolMatrix (Protocol.alice s p₁ p₀).eval
        = diagonal (fun x => if s x then (1 : ℝ) else 0) * boolMatrix p₁.eval
          + diagonal (fun x => if s x then (0 : ℝ) else 1) * boolMatrix p₀.eval := by
      ext x y
      simp only [boolMatrix, eval, Matrix.add_apply, diagonal_mul]
      by_cases hs : s x = true <;> simp [hs]
    rw [hdec]
    calc _ ≤ (diagonal (fun x => if s x then (1 : ℝ) else 0) * boolMatrix p₁.eval).rank
            + (diagonal (fun x => if s x then (0 : ℝ) else 1) * boolMatrix p₀.eval).rank :=
          rank_add_le' _ _
      _ ≤ (boolMatrix p₁.eval).rank + (boolMatrix p₀.eval).rank :=
          Nat.add_le_add (rank_mul_le_right _ _) (rank_mul_le_right _ _)
      _ ≤ 2 ^ p₁.depth + 2 ^ p₀.depth := Nat.add_le_add ih₁ ih₀
      _ ≤ _ := by simpa [depth] using two_pow_add_le p₁.depth p₀.depth
  | bob s p₁ p₀ ih₁ ih₀ =>
    have hdec : boolMatrix (Protocol.bob s p₁ p₀).eval
        = boolMatrix p₁.eval * diagonal (fun y => if s y then (1 : ℝ) else 0)
          + boolMatrix p₀.eval * diagonal (fun y => if s y then (0 : ℝ) else 1) := by
      ext x y
      simp only [boolMatrix, eval, Matrix.add_apply, mul_diagonal]
      by_cases hs : s y = true <;> simp [hs]
    rw [hdec]
    calc _ ≤ (boolMatrix p₁.eval * diagonal (fun y => if s y then (1 : ℝ) else 0)).rank
            + (boolMatrix p₀.eval * diagonal (fun y => if s y then (0 : ℝ) else 1)).rank :=
          rank_add_le' _ _
      _ ≤ (boolMatrix p₁.eval).rank + (boolMatrix p₀.eval).rank :=
          Nat.add_le_add (rank_mul_le_left _ _) (rank_mul_le_left _ _)
      _ ≤ 2 ^ p₁.depth + 2 ^ p₀.depth := Nat.add_le_add ih₁ ih₀
      _ ≤ _ := by simpa [depth] using two_pow_add_le p₁.depth p₀.depth

/-- **Known result** (trivial rank upper bound; Kushilevitz–Nisan, *Communication Complexity*,
Ch. 1–2; Lovász, "Communication complexity: a survey", 1990): every `f` has a protocol of depth
at most `rank M_f + 1`. Fix `r = rank M_f` columns `y₁,…,y_r` spanning the column space of
`M_f`; Alice sends the `r` bits `f x yᵢ`, after which Bob knows row `x` of `M_f` on a column
basis, hence the whole row, and announces `f x y`. -/
theorem exists_protocol_depth_le_rank_add_one [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    ∃ P : Protocol X Y, P.Computes f ∧ P.depth ≤ (boolMatrix f).rank + 1 := by
  classical
  set M := boolMatrix f with hM
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ M.col
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = M.rank := by
    rw [Matrix.rank, Matrix.range_mulVecLin, ← hspan]
    exact (finrank_span_eq_card hli).symm
  have hmem : ∀ y, ∃ c : κ → ℝ, ∑ k, c k • M.col (a k) = M.col y := fun y => by
    have : M.col y ∈ Submodule.span ℝ (Set.range (M.col ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨y, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 this
  choose c hc using hmem
  let e := Fintype.equivFin κ
  let g : X → Fin (Fintype.card κ) → Bool := fun x i => f x (a (e.symm i))
  let h : (Fin (Fintype.card κ) → Bool) → Y → Bool := fun w y =>
    decide (∑ k, c y k * (if w (e k) then (1 : ℝ) else 0) = 1)
  refine ⟨sendThenBob (Fintype.card κ) g h, ?_, ?_⟩
  · intro x y
    rw [eval_sendThenBob]
    have hrow : ∑ k, c y k * M x (a k) = M x y := by
      have := congrFun (hc y) x
      simpa [Finset.sum_apply, Matrix.col] using this
    simp only [h, g, Equiv.symm_apply_apply]
    have : ∑ k, c y k * (if f x (a k) then (1 : ℝ) else 0) = M x y := hrow
    rw [this]
    simp only [hM, boolMatrix]
    cases f x y <;> simp
  · rw [depth_sendThenBob, hcard]

/-- Every `f` on finite domains has some protocol computing it. -/
theorem exists_protocol_cost [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    ∃ d : ℕ, ∃ P : Protocol X Y, P.Computes f ∧ P.depth ≤ d :=
  ⟨_, exists_protocol_depth_le_rank_add_one f⟩

/-- Deterministic communication complexity `D(f)`: the least depth of a protocol computing `f`. -/
noncomputable def detCC [Fintype X] [Fintype Y] (f : X → Y → Bool) : ℕ := by
  classical
  exact Nat.find (exists_protocol_cost f)

theorem detCC_spec [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    ∃ P : Protocol X Y, P.Computes f ∧ P.depth ≤ detCC f := by
  classical
  unfold detCC
  convert Nat.find_spec (exists_protocol_cost f)

theorem detCC_le [Fintype X] [Fintype Y] {f : X → Y → Bool} {P : Protocol X Y}
    (hP : P.Computes f) : detCC f ≤ P.depth := by
  classical
  unfold detCC
  convert Nat.find_min' (exists_protocol_cost f) ⟨P, hP, le_rfl⟩

/-- **Known result** (Mehlhorn–Schmidt 1982; Kushilevitz–Nisan, Lemma 1.28):
`rank M_f ≤ 2 ^ D(f)`. -/
theorem rank_le_two_pow_detCC [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    (boolMatrix f).rank ≤ 2 ^ detCC f := by
  obtain ⟨P, hP, hd⟩ := detCC_spec f
  have hev : P.eval = f := funext fun x => funext fun y => hP x y
  calc (boolMatrix f).rank = (boolMatrix P.eval).rank := by rw [hev]
    _ ≤ 2 ^ P.depth := rank_boolMatrix_eval_le P
    _ ≤ 2 ^ detCC f := Nat.pow_le_pow_right (by norm_num) hd

/-- **Known result** (log-rank lower bound, Mehlhorn–Schmidt 1982):
`⌈log₂ rank M_f⌉ ≤ D(f)`. -/
theorem clog_rank_le_detCC [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    Nat.clog 2 (boolMatrix f).rank ≤ detCC f :=
  Nat.clog_le_of_le_pow (rank_le_two_pow_detCC f)

/-- **Known result** (trivial upper bound, Kushilevitz–Nisan Ch. 1–2; Lovász 1990):
`D(f) ≤ rank M_f + 1`. -/
theorem detCC_le_rank_add_one [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    detCC f ≤ (boolMatrix f).rank + 1 := by
  obtain ⟨P, hP, hd⟩ := exists_protocol_depth_le_rank_add_one f
  exact (detCC_le hP).trans hd

/-- **Log-Rank Conjecture** (Lovász–Saks 1988). OPEN — not proved here.

ProofAtlas exact statement (#7): "There exists a constant `C ≥ 1` such that for every finite
`X`, `Y` and every `f : X × Y → {0,1}`, `D(f) ≤ C · (log₂ (max 2 (rank M_f)))^C`, where `D(f)`
is the deterministic communication complexity of `f` and `M_f` its communication matrix
(rank over `ℝ`)."

Modelling notes: `D(f)` is `detCC` (minimum depth of a deterministic protocol tree, above);
`M_f` is the 0/1 matrix `boolMatrix f` with `Matrix.rank` over `ℝ`; the constant `C` is real
and the exponent is `Real.rpow`. Domains range over `Type` (universe 0), which loses nothing
since only their cardinality matters. Using the ±1 matrix instead changes the rank by at most
one, so the statement is equivalent. The known bounds `clog_rank_le_detCC` and
`detCC_le_rank_add_one` do **not** settle it. -/
def LogRankConjecture : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool),
    (detCC f : ℝ) ≤ C * (Real.logb 2 (max 2 ((boolMatrix f).rank : ℝ))) ^ C

end CryptoLean.OpenProblems.CommComplexity

#print axioms CryptoLean.OpenProblems.CommComplexity.rank_boolMatrix_eval_le
#print axioms CryptoLean.OpenProblems.CommComplexity.exists_protocol_depth_le_rank_add_one
#print axioms CryptoLean.OpenProblems.CommComplexity.rank_le_two_pow_detCC
#print axioms CryptoLean.OpenProblems.CommComplexity.clog_rank_le_detCC
#print axioms CryptoLean.OpenProblems.CommComplexity.detCC_le_rank_add_one
