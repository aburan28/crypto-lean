import Mathlib

/-!
# Coding-theory open problems: #9 (binary Gilbert–Varshamov) and #22 (Shannon capacity)

## Problem #9: asymptotic tightness of the binary Gilbert–Varshamov bound

`A2 n d` is the largest size of a binary code of length `n` and minimum Hamming distance
at least `d` (words are `Fin n → Fin 2`, distance is Mathlib's `hammingDist`).

* Open problem #9 is recorded only as the `Prop` `BinaryGVAsymptoticallyTight` (unproved).
* Proved (known results): the Gilbert–Varshamov bound
  `2ⁿ ≤ A2 n d · ∑_{i<d} C(n,i)` (`gilbert_varshamov`), the Hamming (sphere-packing)
  bound `A2 n (2t+1) · ∑_{i≤t} C(n,i) ≤ 2ⁿ` (`hamming_bound`), and the exact Hamming-ball
  volume `#{w | d(c,w) < r} = ∑_{i<r} C(n,i)` (`card_hammingBall`).

## Problem #22: computability of the Shannon capacity

The `m`-fold strong power `G^⊠m` (`strongPow`) has vertex set `Fin m → V`, two distinct
tuples being adjacent iff they agree-or-are-adjacent in every coordinate. The Shannon
capacity is `Θ(G) = sup_{m ≥ 1} α(G^⊠m)^{1/m}` (`shannonCapacity`), with `α` Mathlib's
`SimpleGraph.indepNum`.

* Open problem #22 is recorded only as the `Prop` `ShannonCapacityComputable` (unproved).
* Proved (known results): `α(G^⊠m) ≤ |V|ᵐ`, `Θ(G) ≤ |V|`, `α(G) ≤ Θ(G)`,
  `α(G^⊠m)^{1/m} ≤ Θ(G)`, `α(C₅) = 2`, `α(C₅ ⊠ C₅) ≥ 5`, and Shannon's lower bound
  `√5 ≤ Θ(C₅)` (`sqrt_five_le_shannonCapacity_cycleGraph_five`).

Neither open problem is resolved here.
-/

namespace CryptoLean.OpenProblems.Coding

open Finset

/-! ## Part 1: binary codes -/

/-- Binary words of length `n`. -/
abbrev Word (n : ℕ) := Fin n → Fin 2

/-- `C` is a binary code of minimum distance at least `d`: distinct codewords are at
Hamming distance `≥ d`. -/
def IsCode {n : ℕ} (d : ℕ) (C : Finset (Word n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y

instance {n d : ℕ} (C : Finset (Word n)) : Decidable (IsCode d C) := by
  unfold IsCode; infer_instance

/-- `A2 n d`: the maximum size of a binary code of length `n` and minimum distance `≥ d`. -/
def A2 (n d : ℕ) : ℕ :=
  ((univ : Finset (Finset (Word n))).filter (IsCode d)).sup Finset.card

theorem card_le_A2 {n d : ℕ} {C : Finset (Word n)} (hC : IsCode d C) : C.card ≤ A2 n d :=
  Finset.le_sup (f := Finset.card) (mem_filter.2 ⟨mem_univ _, hC⟩)

theorem exists_code_card_eq_A2 (n d : ℕ) : ∃ C : Finset (Word n), IsCode d C ∧ C.card = A2 n d := by
  have hne : ((univ : Finset (Finset (Word n))).filter (IsCode d)).Nonempty :=
    ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [IsCode]⟩⟩
  obtain ⟨C, hC, hCeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨C, (mem_filter.1 hC).2, hCeq.symm⟩

/-- Number of subsets of `Fin n` of size `< r`. -/
theorem card_finset_card_lt (n r : ℕ) :
    ((univ : Finset (Finset (Fin n))).filter (fun s => s.card < r)).card =
      ∑ i ∈ range r, n.choose i := by
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range r)
    (by intro s hs; simpa using hs)]
  refine sum_congr rfl fun i hi => ?_
  have : ((univ.filter (fun s : Finset (Fin n) => s.card < r)).filter
      (fun s => s.card = i)) = powersetCard i (univ : Finset (Fin n)) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨by rw [h]; simpa using hi, h⟩
  rw [this, card_powersetCard, card_univ, Fintype.card_fin]

/-- The positions where `w` differs from `c`. -/
def diffSet {n : ℕ} (c w : Word n) : Finset (Fin n) := univ.filter (fun i => c i ≠ w i)

/-- Flip the bits of `c` on the positions in `s`. -/
def flipOn {n : ℕ} (c : Word n) (s : Finset (Fin n)) : Word n :=
  fun i => if i ∈ s then c i + 1 else c i

theorem hammingDist_eq_card_diffSet {n : ℕ} (c w : Word n) :
    hammingDist c w = (diffSet c w).card := rfl

theorem flipOn_diffSet {n : ℕ} (c w : Word n) : flipOn c (diffSet c w) = w := by
  funext i
  have key : ∀ a b : Fin 2, (if a ≠ b then a + 1 else a) = b := by decide
  simpa [flipOn, diffSet] using key (c i) (w i)

theorem diffSet_flipOn {n : ℕ} (c : Word n) (s : Finset (Fin n)) : diffSet c (flipOn c s) = s := by
  ext i
  have key : ∀ a : Fin 2, a ≠ a + 1 := by decide
  by_cases h : i ∈ s <;> simp [diffSet, flipOn, h, key]

/-- **Known result** (volume of a binary Hamming ball): the number of binary words at
Hamming distance `< r` from a fixed word is `∑_{i<r} C(n,i)`. Standard; e.g.
MacWilliams–Sloane, *The Theory of Error-Correcting Codes*, Ch. 1. -/
theorem card_hammingBall {n : ℕ} (c : Word n) (r : ℕ) :
    ((univ : Finset (Word n)).filter (fun w => hammingDist c w < r)).card =
      ∑ i ∈ range r, n.choose i := by
  rw [← card_finset_card_lt]
  refine Finset.card_bij' (fun w _ => diffSet c w) (fun s _ => flipOn c s) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    rw [hammingDist_eq_card_diffSet] at hw; exact hw
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    rw [hammingDist_eq_card_diffSet, diffSet_flipOn]; exact hs
  · intro w _; exact flipOn_diffSet c w
  · intro s _; exact diffSet_flipOn c s

/-- **Known result: the Gilbert–Varshamov bound** (Gilbert 1952, Varshamov 1957; see
MacWilliams–Sloane Ch. 1, Thm. 12 / Roth, *Introduction to Coding Theory*, Thm. 4.10):
for `d ≥ 1`, `A₂(n,d) · ∑_{i=0}^{d-1} C(n,i) ≥ 2ⁿ`. Proof: the radius-`(d-1)` balls
around a maximum code cover `{0,1}ⁿ`. -/
theorem gilbert_varshamov (n d : ℕ) (hd : 1 ≤ d) :
    2 ^ n ≤ A2 n d * ∑ i ∈ range d, n.choose i := by
  obtain ⟨C, hC, hCcard⟩ := exists_code_card_eq_A2 n d
  have cover : (univ : Finset (Word n)) ⊆
      C.biUnion (fun c => univ.filter (fun w => hammingDist c w < d)) := by
    intro w _
    by_contra hw
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, not_exists, not_and,
      not_lt] at hw
    have hwC : w ∉ C := by
      intro hm; have := hw w hm; simp at this; omega
    have hcode : IsCode d (insert w C) := by
      intro x hx y hy hxy
      rw [mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · rw [hammingDist_comm]; exact hw y hy
      · exact hw x hx
      · exact hC x hx y hy hxy
    have := card_le_A2 hcode
    rw [card_insert_of_notMem hwC] at this
    omega
  calc 2 ^ n = (univ : Finset (Word n)).card := by simp
    _ ≤ (C.biUnion (fun c => univ.filter (fun w => hammingDist c w < d))).card :=
        card_le_card cover
    _ ≤ ∑ c ∈ C, (univ.filter (fun w => hammingDist c w < d)).card := card_biUnion_le
    _ = A2 n d * ∑ i ∈ range d, n.choose i := by
        simp only [card_hammingBall, sum_const, smul_eq_mul, hCcard]

/-- **Known result: the Hamming (sphere-packing) bound** (Hamming 1950; MacWilliams–Sloane
Ch. 1, Thm. 6): `A₂(n, 2t+1) · ∑_{i=0}^{t} C(n,i) ≤ 2ⁿ`. Proof: radius-`t` balls around
the codewords of a code of minimum distance `2t+1` are pairwise disjoint. -/
theorem hamming_bound (n t : ℕ) :
    A2 n (2 * t + 1) * ∑ i ∈ range (t + 1), n.choose i ≤ 2 ^ n := by
  obtain ⟨C, hC, hCcard⟩ := exists_code_card_eq_A2 n (2 * t + 1)
  have disj : (C : Set (Word n)).PairwiseDisjoint
      (fun c => univ.filter (fun w => hammingDist c w < t + 1)) := by
    intro x hx y hy hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwx hwy
    simp only [mem_filter, mem_univ, true_and] at hwx hwy
    have h1 := hC x hx y hy hxy
    have h2 := hammingDist_triangle x w y
    rw [hammingDist_comm w y] at h2
    omega
  calc A2 n (2 * t + 1) * ∑ i ∈ range (t + 1), n.choose i
      = ∑ c ∈ C, (univ.filter (fun w => hammingDist c w < t + 1)).card := by
        simp only [card_hammingBall, sum_const, smul_eq_mul, hCcard]
    _ = (C.biUnion (fun c => univ.filter (fun w => hammingDist c w < t + 1))).card :=
        (card_biUnion disj).symm
    _ ≤ (univ : Finset (Word n)).card := card_le_univ _
    _ = 2 ^ n := by simp

/-- The asymptotic rate `R(δ) = limsup_{n→∞} (1/n) log₂ A₂(n, ⌈δ n⌉)`. -/
noncomputable def binaryRate (δ : ℝ) : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (A2 n ⌈δ * n⌉₊) / n) Filter.atTop

/-- **Open problem #9 (ProofAtlas rank 138): asymptotic tightness of the binary
Gilbert–Varshamov bound.** Standard statement (ProofAtlas text not available offline):
"Is the asymptotic Gilbert–Varshamov bound tight for binary codes, i.e. is
`R(δ) = 1 − H₂(δ)` for all `0 < δ < 1/2`, where
`R(δ) = limsup_{n→∞} (1/n) log₂ A₂(n, δn)`?"
Known: `R(δ) ≥ 1 − H₂(δ)` (Gilbert–Varshamov) and `R(δ) ≤` the MRRW linear-programming
bound, which is strictly larger than `1 − H₂(δ)`; the question is OPEN.

Modelling: the binary entropy `H₂(δ)` is Mathlib's `Real.binEntropy δ` (natural log)
divided by `log 2`; the distance `δn` is rounded up to `⌈δ n⌉₊` (rounding does not affect
the asymptotic rate). This `Prop` is not proved here. -/
def BinaryGVAsymptoticallyTight : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → binaryRate δ = 1 - Real.binEntropy δ / Real.log 2

/-! ## Part 2: Shannon capacity -/

/-- The `m`-fold strong power `G^⊠m`: distinct tuples `x ≠ y` are adjacent iff in every
coordinate `x i = y i` or `x i ~ y i`. -/
def strongPow {V : Type*} (G : SimpleGraph V) (m : ℕ) : SimpleGraph (Fin m → V) where
  Adj x y := x ≠ y ∧ ∀ i, x i = y i ∨ G.Adj (x i) (y i)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, fun i => (h i).elim (fun e => Or.inl e.symm)
    (fun a => Or.inr a.symm)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) :
    DecidableRel (strongPow G m).Adj := fun x y => by
  unfold strongPow; infer_instance

/-- The Shannon capacity `Θ(G) = sup_{m ≥ 1} α(G^⊠m)^{1/m}` (indexed here by `m + 1`,
`m : ℕ`). -/
noncomputable def shannonCapacity {V : Type*} (G : SimpleGraph V) : ℝ :=
  ⨆ m : ℕ, ((strongPow G (m + 1)).indepNum : ℝ) ^ (((m + 1 : ℕ) : ℝ)⁻¹)

/-- **Known result** (trivial bound): `α(G^⊠m) ≤ |V|ᵐ`. -/
theorem indepNum_strongPow_le {V : Type*} [Fintype V] (G : SimpleGraph V) (m : ℕ) :
    (strongPow G m).indepNum ≤ Fintype.card V ^ m := by
  classical
  obtain ⟨s, hs⟩ := (strongPow G m).exists_isNIndepSet_indepNum
  rw [← hs.card_eq]
  simpa using card_le_univ s

/-- **Known result** (trivial bound, Shannon 1956): `Θ(G) ≤ |V|`. -/
theorem shannonCapacity_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) :
    shannonCapacity G ≤ Fintype.card V := by
  apply ciSup_le
  intro m
  have hk : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  calc ((strongPow G (m + 1)).indepNum : ℝ) ^ (((m + 1 : ℕ) : ℝ)⁻¹)
      ≤ ((Fintype.card V : ℝ) ^ (m + 1)) ^ (((m + 1 : ℕ) : ℝ)⁻¹) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast indepNum_strongPow_le G (m + 1)
    _ = Fintype.card V := Real.pow_rpow_inv_natCast (by positivity) (by omega)

theorem bddAbove_shannon {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove (Set.range fun m : ℕ =>
      ((strongPow G (m + 1)).indepNum : ℝ) ^ (((m + 1 : ℕ) : ℝ)⁻¹)) := by
  refine ⟨Fintype.card V, ?_⟩
  rintro _ ⟨m, rfl⟩
  exact (le_ciSup_of_le (bddAbove_def.2 ⟨(Fintype.card V : ℝ), by
    rintro _ ⟨k, rfl⟩
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    calc ((strongPow G (k + 1)).indepNum : ℝ) ^ (((k + 1 : ℕ) : ℝ)⁻¹)
        ≤ ((Fintype.card V : ℝ) ^ (k + 1)) ^ (((k + 1 : ℕ) : ℝ)⁻¹) := by
          apply Real.rpow_le_rpow (by positivity) _ (by positivity)
          exact_mod_cast indepNum_strongPow_le G (k + 1)
      _ = Fintype.card V := Real.pow_rpow_inv_natCast (by positivity) (by omega)⟩)
    m le_rfl).trans (shannonCapacity_le_card G)

/-- **Known result** (Shannon 1956): `α(G^⊠m)^{1/m} ≤ Θ(G)` for every `m ≥ 1`. -/
theorem rpow_indepNum_le_shannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m : ℕ) (hm : 1 ≤ m) :
    ((strongPow G m).indepNum : ℝ) ^ ((m : ℝ)⁻¹) ≤ shannonCapacity G := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact le_ciSup (bddAbove_shannon G) k

/-- **Known result** (Shannon 1956): `α(G) ≤ Θ(G)`. -/
theorem indepNum_le_shannonCapacity {V : Type*} [Fintype V] (G : SimpleGraph V) :
    (G.indepNum : ℝ) ≤ shannonCapacity G := by
  classical
  have h1 := rpow_indepNum_le_shannonCapacity G 1 le_rfl
  simp only [Nat.cast_one, inv_one, Real.rpow_one] at h1
  refine le_trans ?_ h1
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  let f : V ↪ (Fin 1 → V) := ⟨fun v _ => v, fun v w h => congrFun h 0⟩
  have hind : (strongPow G 1).IsIndepSet (s.map f : Set (Fin 1 → V)) := by
    intro x hx y hy hxy hadj
    simp only [coe_map, Set.mem_image, mem_coe] at hx hy
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    have hvw : v ≠ w := fun h => hxy (by rw [h])
    rcases hadj.2 0 with h | h
    · exact hvw h
    · exact hs.isIndepSet hv hw hvw h
  have := hind.card_le_indepNum
  rw [card_map, hs.card_eq] at this
  exact_mod_cast this

/-- **Known result**: `α(C₅) = 2` (Shannon 1956). -/
theorem indepNum_cycleGraph_five : (SimpleGraph.cycleGraph 5).indepNum = 2 := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (SimpleGraph.cycleGraph 5).exists_isNIndepSet_indepNum
    rw [← hs.card_eq]
    have key : ∀ t : Finset (Fin 5), (SimpleGraph.cycleGraph 5).IsIndepSet (t : Set (Fin 5)) →
        t.card ≤ 2 := by decide
    exact key s hs.isIndepSet
  · have : (SimpleGraph.cycleGraph 5).IsIndepSet (({0, 2} : Finset (Fin 5)) : Set (Fin 5)) := by
      decide
    simpa using this.card_le_indepNum

/-- The independent set `{(i, 2i mod 5)}` of `C₅ ⊠ C₅`. -/
def shannonSet : Finset (Fin 2 → Fin 5) :=
  univ.image (fun i : Fin 5 => ![i, 2 * i])

/-- **Known result** (Shannon 1956): `α(C₅ ⊠ C₅) ≥ 5`, witnessed by `{(i, 2i mod 5)}`. -/
theorem five_le_indepNum_strongPow_two :
    5 ≤ (strongPow (SimpleGraph.cycleGraph 5) 2).indepNum := by
  have hind : (strongPow (SimpleGraph.cycleGraph 5) 2).IsIndepSet (shannonSet : Set _) := by
    decide
  have hcard : shannonSet.card = 5 := by decide
  rw [← hcard]; exact hind.card_le_indepNum

/-- **Known result** (Shannon 1956): `√5 ≤ Θ(C₅)`. (Lovász 1979 proved equality; that
upper bound is not formalized here.) -/
theorem sqrt_five_le_shannonCapacity_cycleGraph_five :
    Real.sqrt 5 ≤ shannonCapacity (SimpleGraph.cycleGraph 5) := by
  refine le_trans ?_ (rpow_indepNum_le_shannonCapacity _ 2 (by norm_num))
  rw [Real.sqrt_eq_rpow, show ((2 : ℕ) : ℝ)⁻¹ = 1 / 2 by norm_num]
  apply Real.rpow_le_rpow (by norm_num) _ (by norm_num)
  exact_mod_cast five_le_indepNum_strongPow_two

/-! ### The computability question -/

/-- Decode a finite graph from `(n, E)`: vertices `Fin n`, `i ~ j` iff `i ≠ j` and
`(i, j) ∈ E` or `(j, i) ∈ E`. -/
def graphOf (n : ℕ) (E : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => (i.val, j.val) ∈ E

/-- Every finite simple graph on `Fin n` is encoded by some edge list (the encoding used
in `ShannonCapacityComputable` covers all finite graphs up to relabelling). -/
theorem graphOf_surjective (n : ℕ) (G : SimpleGraph (Fin n)) : ∃ E, graphOf n E = G := by
  classical
  refine ⟨((univ ×ˢ univ).filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).toList.map
    (fun p => (p.1.val, p.2.val)), ?_⟩
  ext i j
  simp only [graphOf, SimpleGraph.fromRel_adj, List.mem_map, mem_toList, mem_filter,
    mem_product, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨hne, ⟨p, hp, h1, h2⟩ | ⟨p, hp, h1, h2⟩⟩
    · have : p = (i, j) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      subst this; exact hp
    · have : p = (j, i) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      subst this; exact hp.symm
  · intro h
    exact ⟨h.ne, Or.inl ⟨(i, j), h, rfl, rfl⟩⟩

/-- **Open problem #22 (ProofAtlas rank 325): computability of the Shannon capacity.**
Standard statement (ProofAtlas text not available offline): "Is the Shannon capacity
`Θ(G) = sup_m α(G^⊠m)^{1/m}` of a finite graph computable?" (Asked e.g. by Alon and by
Lovász; it is not even known whether `Θ(C₇)` is computable to arbitrary precision.)
The question is OPEN.

Modelling: we formalize the uniform version — there is a computable (Mathlib
`Computable`) map taking an encoded graph `(n, E)` (see `graphOf`, which reaches every
graph on `Fin n`, `graphOf_surjective`) and a precision `k` to a rational `a / (b + 1)`
(returned as `(a, b) : ℤ × ℕ`) within `1/(k+1)` of `Θ(graphOf n E)`. A non-uniform variant
(each `Θ(G)` is a computable real) is weaker and also open. This `Prop` is not proved. -/
def ShannonCapacityComputable : Prop :=
  ∃ f : (ℕ × List (ℕ × ℕ)) × ℕ → ℤ × ℕ, Computable f ∧
    ∀ (n : ℕ) (E : List (ℕ × ℕ)) (k : ℕ),
      |((f ((n, E), k)).1 : ℝ) / ((f ((n, E), k)).2 + 1) - shannonCapacity (graphOf n E)|
        ≤ 1 / (k + 1)

end CryptoLean.OpenProblems.Coding

#print axioms CryptoLean.OpenProblems.Coding.card_hammingBall
#print axioms CryptoLean.OpenProblems.Coding.gilbert_varshamov
#print axioms CryptoLean.OpenProblems.Coding.hamming_bound
#print axioms CryptoLean.OpenProblems.Coding.indepNum_strongPow_le
#print axioms CryptoLean.OpenProblems.Coding.shannonCapacity_le_card
#print axioms CryptoLean.OpenProblems.Coding.rpow_indepNum_le_shannonCapacity
#print axioms CryptoLean.OpenProblems.Coding.indepNum_le_shannonCapacity
#print axioms CryptoLean.OpenProblems.Coding.indepNum_cycleGraph_five
#print axioms CryptoLean.OpenProblems.Coding.five_le_indepNum_strongPow_two
#print axioms CryptoLean.OpenProblems.Coding.sqrt_five_le_shannonCapacity_cycleGraph_five
#print axioms CryptoLean.OpenProblems.Coding.graphOf_surjective
