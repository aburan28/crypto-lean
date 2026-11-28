import Mathlib

/-!
# Open problem #207: capacity of the binary deletion channel

## The channel model

An input word of length `n` is `x : Fin n → Bool`. A *deletion pattern* is
`s : Fin n → Bool` (`s i = true` means bit `i` is deleted). The channel output is the list
of surviving bits in their original order (`delOutput x s`). Each bit is deleted
independently with probability `d`, so pattern `s` has probability
`∏ i, (if s i then d else 1 - d)` (`patternProb`), and
`W_d(y | x) = ∑_{s : delOutput x s = y} patternProb d s` (`delChannel`).
The decoder sees only the output list `y`, never `s`.

A code of length `n` with `M` messages (`DelCode n M`) is an encoder
`Fin M → (Fin n → Bool)` and a decoder `List Bool → Fin M`; its average error probability
is `avgError`. A rate `R` is achievable (`Achievable d R`) if for every `ε > 0` and every
large enough `n` there is a code with at least `2^{Rn}` messages and average error `≤ ε`;
`capDel d` is the supremum of achievable rates.

* Open problem #207 ("determine `C_del(d)`") is recorded only as the unproved `Prop`
  `DeletionCapacityDetermined`, parametrized by the class of admissible "explicit"
  answers (see its docstring for why).
* Proved sanity facts about the model (not the open problem): the pattern probabilities
  sum to `1` (`sum_patternProb`), and with `d = 0` the channel is the identity
  (`delChannel_zero`); rate `0` is achievable (`achievable_zero`).

## Known combinatorial result: Varshamov–Tenengolts codes

`VT_a(n) = {x ∈ {0,1}ⁿ : ∑_{i=1}^n i·xᵢ ≡ a (mod n+1)}` (`vtCode`).

* `vtCode_single_deletion` (Levenshtein 1965): two distinct codewords of `VT_a(n)` have no
  common subsequence of length `n - 1`, i.e. `VT_a(n)` corrects any single deletion.
* `exists_vtCode_card` (pigeonhole): some `a` has `2ⁿ ≤ (n+1)·|VT_a(n)|`.

Nothing here resolves, or suggests a resolution of, open problem #207.
-/

namespace CryptoLean.OpenProblems.Deletion

open Finset
open scoped List

/-! ## Part 1: Varshamov–Tenengolts codes (Levenshtein 1965) -/


/-- The VT checksum of a list, defined recursively from the front:
`vtL (b :: l) = b + vtL l + List.count true l`. `vtL_eq_sum` shows it equals `∑_{i=1}^{|l|} i·lᵢ`. -/
def vtL : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + vtL l + List.count true l

theorem vtL_append (u v : List Bool) : vtL (u ++ v) = vtL u + vtL v + u.length * List.count true v := by
  induction u with
  | nil => simp [vtL]
  | cons a u ih =>
    simp only [List.cons_append, vtL, ih, List.count_append, List.length_cons]
    ring

/-- The VT checksum `∑_{i=1}^n i·xᵢ` of a word `x ∈ {0,1}ⁿ` (positions are 1-indexed). -/
def vtSyndrome {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, (i.val + 1) * (x i).toNat

theorem wt_ofFn {n : ℕ} (x : Fin n → Bool) : List.count true (List.ofFn x) = ∑ i : Fin n, (x i).toNat := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, ih]
    cases x 0 <;> simp; ring

theorem vtL_ofFn {n : ℕ} (x : Fin n → Bool) : vtL (List.ofFn x) = vtSyndrome x := by
  induction n with
  | zero => simp [vtL, vtSyndrome]
  | succ n ih =>
    rw [List.ofFn_succ, vtL, ih, wt_ofFn, vtSyndrome, vtSyndrome, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, zero_add, one_mul]
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-- The Varshamov–Tenengolts code `VT_a(n) = {x ∈ {0,1}ⁿ : ∑ i·xᵢ ≡ a (mod n+1)}`. -/
def vtCode (n : ℕ) (a : ZMod (n + 1)) : Finset (Fin n → Bool) :=
  univ.filter fun x => ((vtSyndrome x : ℕ) : ZMod (n + 1)) = a

/-- If a sublist `z` of `x` is exactly one shorter, it arises by deleting one entry. -/
theorem exists_delete_of_sublist {z x : List Bool} (h : z <+ x) (hl : x.length = z.length + 1) :
    ∃ u b v, x = u ++ b :: v ∧ z = u ++ v := by
  induction h with
  | slnil => simp at hl
  | @cons l₁ l₂ a h _ =>
    exact ⟨[], a, l₂, rfl, (h.eq_of_length (by simp at hl; omega)).symm ▸ rfl⟩
  | @cons_cons l₁ l₂ a _ ih =>
    obtain ⟨u, b, v, rfl, rfl⟩ := ih (by simpa using hl)
    exact ⟨a :: u, b, v, rfl, rfl⟩

/-- Increase of the VT checksum when a bit `b` is inserted between `u` and `v`. -/
def delta (u : List Bool) (b : Bool) (v : List Bool) : ℕ := b.toNat * (u.length + 1) + List.count true v

theorem vtL_insert (u : List Bool) (b : Bool) (v : List Bool) :
    vtL (u ++ b :: v) = vtL (u ++ v) + delta u b v := by
  rw [vtL_append, vtL_append, vtL, delta, List.count_cons]
  cases b <;> simp <;> ring

/-- Inserting `b` into a run of `b`s: the position inside the run does not matter. -/
theorem insert_run (u m v : List Bool) (b : Bool) (hm : ∀ c ∈ m, c = b) :
    u ++ b :: (m ++ v) = (u ++ m) ++ b :: v := by
  have : m = List.replicate m.length b := List.eq_replicate_iff.2 ⟨rfl, hm⟩
  rw [this, List.append_assoc]
  congr 1
  rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ', List.append_assoc]
  rfl

theorem insert_eq_of_delta_eq_aux (u m v : List Bool) (b : Bool)
    (h : delta u b (m ++ v) = delta (u ++ m) b v) :
    u ++ b :: (m ++ v) = (u ++ m) ++ b :: v := by
  apply insert_run _ _ _ b
  cases b
  · -- inserting a `0`: the run `m` has no ones
    simp only [delta, Bool.toNat_false, zero_mul, zero_add, List.count_append] at h
    have h0 : m.count true = 0 := by omega
    intro c hc
    cases c
    · rfl
    · exact absurd (List.count_pos_iff.2 hc) (by omega)
  · -- inserting a `1`: the run `m` has no zeros
    simp only [delta, Bool.toNat_true, one_mul, List.count_append, List.length_append] at h
    have h1 : m.count true = m.length := by omega
    intro c hc
    exact (List.count_eq_length.1 h1 c hc).symm

/-- Two single insertions of the same bit into the same word with the same checksum
increase give the same word. -/
theorem insert_eq_of_delta_eq {u₁ v₁ u₂ v₂ : List Bool} (b : Bool) (he : u₁ ++ v₁ = u₂ ++ v₂)
    (h : delta u₁ b v₁ = delta u₂ b v₂) : u₁ ++ b :: v₁ = u₂ ++ b :: v₂ := by
  rcases List.append_eq_append_iff.1 he with ⟨m, rfl, rfl⟩ | ⟨m, rfl, rfl⟩
  · exact insert_eq_of_delta_eq_aux u₁ m v₂ b h
  · exact (insert_eq_of_delta_eq_aux u₂ m v₁ b h.symm).symm

theorem delta_false_le (u v : List Bool) : delta u false v ≤ List.count true (u ++ v) := by
  simp [delta, List.count_append]

theorem delta_true_gt (u v : List Bool) : List.count true (u ++ v) < delta u true v := by
  have := List.count_le_length (a := true) (l := u)
  simp only [delta, List.count_append, Bool.toNat_true, one_mul]
  omega

theorem delta_le (u : List Bool) (b : Bool) (v : List Bool) :
    delta u b v ≤ (u ++ v).length + 1 := by
  have := List.count_le_length (a := true) (l := v)
  cases b <;> simp [delta] <;> omega

/-- Single-deletion correction for lists: two words of length `n` with VT checksums
congruent modulo `n + 1` that share a subsequence of length `n - 1` are equal. -/
theorem eq_of_vtL_modEq {n : ℕ} {x y z : List Bool} (hx : x.length = n) (hy : y.length = n)
    (hxy : vtL x ≡ vtL y [MOD n + 1]) (hzx : z <+ x) (hzy : z <+ y)
    (hz : z.length + 1 = n) : x = y := by
  obtain ⟨u₁, b₁, v₁, rfl, rfl⟩ := exists_delete_of_sublist hzx (by omega)
  obtain ⟨u₂, b₂, v₂, rfl, he⟩ := exists_delete_of_sublist hzy (by omega)
  rw [vtL_insert, vtL_insert, he] at hxy
  have hd : delta u₁ b₁ v₁ = delta u₂ b₂ v₂ := by
    have h1 := delta_le u₁ b₁ v₁
    have h2 := delta_le u₂ b₂ v₂
    rw [he] at h1 hz
    have := Nat.ModEq.add_left_cancel' _ hxy
    exact Nat.ModEq.eq_of_lt_of_lt this (by omega) (by omega)
  have hb : b₁ = b₂ := by
    have := delta_false_le u₁ v₁; have := delta_true_gt u₁ v₁
    have := delta_false_le u₂ v₂; have := delta_true_gt u₂ v₂
    rw [he] at *
    cases b₁ <;> cases b₂ <;> first | rfl | omega
  subst hb
  exact insert_eq_of_delta_eq b₁ he hd

/-- **Known result (Levenshtein 1965; Varshamov–Tenengolts 1965).** The VT code
`VT_a(n) = {x ∈ {0,1}ⁿ : ∑_{i=1}^n i·xᵢ ≡ a (mod n+1)}` corrects a single deletion: two
distinct codewords have no common subsequence of length `n - 1`.
[V. I. Levenshtein, "Binary codes capable of correcting deletions, insertions, and
reversals", Dokl. Akad. Nauk SSSR 163 (1965); Soviet Physics Doklady 10 (1966) 707–710.] -/
theorem vtCode_single_deletion {n : ℕ} (a : ZMod (n + 1)) {x y : Fin n → Bool}
    (hx : x ∈ vtCode n a) (hy : y ∈ vtCode n a) (hxy : x ≠ y) :
    ¬ ∃ z : List Bool, z.length = n - 1 ∧ z <+ List.ofFn x ∧ z <+ List.ofFn y := by
  rintro ⟨z, hz, hzx, hzy⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hxy (funext fun i => i.elim0)
  apply hxy
  have hmod : vtL (List.ofFn x) ≡ vtL (List.ofFn y) [MOD n + 1] := by
    rw [vtL_ofFn, vtL_ofFn, ← ZMod.natCast_eq_natCast_iff]
    simp only [vtCode, mem_filter, mem_univ, true_and] at hx hy
    rw [hx, hy]
  have := eq_of_vtL_modEq (List.length_ofFn) (List.length_ofFn) hmod hzx hzy (by omega)
  exact List.ofFn_injective this

/-- **Known result (pigeonhole; Varshamov–Tenengolts 1965).** For every `n` some VT code
`VT_a(n)` has at least `2ⁿ/(n+1)` codewords, stated without division as
`2ⁿ ≤ (n+1)·|VT_a(n)|`. [R. R. Varshamov, G. M. Tenengolts, Avtomatika i Telemekhanika
26 (1965); see also N. J. A. Sloane, "On single-deletion-correcting codes" (2002).] -/
theorem exists_vtCode_card (n : ℕ) : ∃ a : ZMod (n + 1), 2 ^ n ≤ (n + 1) * (vtCode n a).card := by
  by_contra h
  push Not at h
  have hsum : ∑ a : ZMod (n + 1), (vtCode n a).card = 2 ^ n := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin n → Bool => ((vtSyndrome x : ℕ) : ZMod (n + 1)))
      (s := univ) (t := univ) (fun _ _ => mem_univ _)
    simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    rw [this]; rfl
  have : ∑ a : ZMod (n + 1), (n + 1) * (vtCode n a).card < ∑ _a : ZMod (n + 1), 2 ^ n :=
    Finset.sum_lt_sum_of_nonempty univ_nonempty fun a _ => h a
  rw [← Finset.mul_sum, hsum, sum_const, card_univ, ZMod.card, smul_eq_mul] at this
  exact lt_irrefl _ this

/-- Real-valued form: some `a` has `|VT_a(n)| ≥ 2ⁿ/(n+1)`. -/
theorem exists_vtCode_card_real (n : ℕ) :
    ∃ a : ZMod (n + 1), (2 : ℝ) ^ n / (n + 1) ≤ (vtCode n a).card := by
  obtain ⟨a, ha⟩ := exists_vtCode_card n
  refine ⟨a, (div_le_iff₀ (by positivity)).2 ?_⟩
  rw [mul_comm]; exact_mod_cast ha

/-! ## Part 2: the binary deletion channel and its capacity -/

/-- Channel output for input `x` and deletion pattern `s` (`s i = true`: bit `i` deleted):
the surviving bits, in their original order. -/
def delOutput {n : ℕ} (x s : Fin n → Bool) : List Bool :=
  ((List.finRange n).filter fun i => !s i).map x

/-- Probability of deletion pattern `s` when each bit is deleted independently with
probability `d`. -/
noncomputable def patternProb {n : ℕ} (d : ℝ) (s : Fin n → Bool) : ℝ :=
  ∏ i, if s i then d else 1 - d

/-- Transition probability `W_d(y | x)` of the binary deletion channel: the total
probability of the deletion patterns that turn `x` into `y`. -/
noncomputable def delChannel {n : ℕ} (d : ℝ) (x : Fin n → Bool) (y : List Bool) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Fin n → Bool => delOutput x s = y), patternProb d s

/-- A deterministic block code for the deletion channel: `M` messages, input length `n`.
The decoder sees only the received list (of any length), not the deletion pattern. -/
structure DelCode (n M : ℕ) where
  enc : Fin M → Fin n → Bool
  dec : List Bool → Fin M

/-- Average (over uniformly chosen messages) error probability of a code on the deletion
channel with deletion probability `d`. -/
noncomputable def avgError {n M : ℕ} (d : ℝ) (C : DelCode n M) : ℝ :=
  (M : ℝ)⁻¹ * ∑ m : Fin M, ∑ s : Fin n → Bool,
    patternProb d s * if C.dec (delOutput (C.enc m) s) = m then 0 else 1

/-- `R` (bits per input bit) is an achievable rate: for every `ε > 0`, for all large enough
block lengths `n` there is a code with at least `2^{R n}` messages and average error at
most `ε`. -/
def Achievable (d R : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ M : ℕ, (2 : ℝ) ^ (R * n) ≤ M ∧
    ∃ C : DelCode n M, avgError d C ≤ ε

/-- The (average-error Shannon) capacity `C_del(d) = sup {R | R achievable}` of the binary
deletion channel, in bits per input bit.

Modelling note: Mathlib's `sSup` on `ℝ` returns `0` for sets that are not bounded above;
the known converse `C_del(d) ≤ 1 - d` (which makes the set bounded) is NOT formalized
here, so this definition agrees with the true capacity only given that standard fact.
The set is nonempty (`achievable_zero`). -/
noncomputable def capDel (d : ℝ) : ℝ := sSup {R : ℝ | Achievable d R}

/-- **Open problem #207 (ProofAtlas, edition 2026-11-12): capacity of the binary deletion
channel.** Exact statement: "Determine the exact average-error Shannon capacity
C_del(d), in bits per input bit, of the binary deletion channel for every real d with
0<d<1. Each input bit is independently deleted with probability d; surviving bits retain
their order, and neither terminal observes the deletion pattern."

The question is OPEN; it is not resolved here. Known (not formalized here): Dobrushin's
coding theorem `C_del(d) = lim_n max_{P_{Xⁿ}} I(Xⁿ; Y)/n`, the bounds
`max(1 - H₂(d), (1-d)/9) ≤ C_del(d) ≤ 1 - d` and many sharper numerical bounds.

Modelling: "determine" is a request for an explicit answer, not a single mathematical
proposition. We therefore record it as a `Prop` parametrized by the class `Explicit` of
functions `ℝ → ℝ` one is willing to accept as an explicit determination (e.g. closed-form
elementary expressions, or functions given by a specified finite formula); choosing that
class is outside the scope of the formalization. The `Prop` says some admissible `f`
agrees with `capDel` on `(0,1)`. With `Explicit = Set.univ` it is trivially true
(`f = capDel`), so all mathematical content lies in a meaningful choice of `Explicit`.
The channel model is `delChannel`/`avgError`/`Achievable`/`capDel` above: deterministic
encoders, deterministic decoders seeing only the output list, uniform messages, and rate
measured as `log₂ M / n` via the requirement `M ≥ 2^{Rn}`. Neither the encoder nor the
decoder has access to the deletion pattern `s`. See `capDel` for the `sSup` convention. -/
def DeletionCapacityDetermined (Explicit : Set (ℝ → ℝ)) : Prop :=
  ∃ f ∈ Explicit, ∀ d : ℝ, 0 < d → d < 1 → capDel d = f d

/-- Sanity fact about the model: the deletion-pattern probabilities sum to `1`. -/
theorem sum_patternProb (n : ℕ) (d : ℝ) : ∑ s : Fin n → Bool, patternProb d s = 1 := by
  have := Finset.prod_univ_sum (t := fun (_ : Fin n) => (univ : Finset Bool))
    (f := fun _ b => if b then d else 1 - d)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_sub_cancel,
    prod_const_one, Fintype.piFinset_univ] at this
  rw [this]
  rfl

/-- Sanity fact about the model: for every input, the output probabilities sum to `1`. -/
theorem sum_delChannel {n : ℕ} (d : ℝ) (x : Fin n → Bool) :
    ∑ y ∈ univ.image (delOutput x), delChannel d x y = 1 := by
  rw [← sum_patternProb n d]
  simp only [delChannel]
  exact Finset.sum_fiberwise_of_maps_to (g := delOutput x)
    (fun s _ => mem_image_of_mem _ (mem_univ s)) _

theorem delOutput_false {n : ℕ} (x : Fin n → Bool) :
    delOutput x (fun _ => false) = List.ofFn x := by
  simp [delOutput, List.ofFn_eq_map]

theorem patternProb_zero {n : ℕ} (s : Fin n → Bool) :
    patternProb 0 s = if s = (fun _ => false) then 1 else 0 := by
  split_ifs with h
  · subst h; simp [patternProb]
  · obtain ⟨i, hi⟩ : ∃ i, s i ≠ false := by
      by_contra h'; push Not at h'; exact h (funext h')
    exact Finset.prod_eq_zero (mem_univ i) (by simp_all)

/-- Sanity fact about the model (zero-deletion case): with `d = 0` the deletion channel is
noiseless, delivering the input word with probability `1`. -/
theorem delChannel_zero {n : ℕ} (x : Fin n → Bool) (y : List Bool) :
    delChannel 0 x y = if y = List.ofFn x then 1 else 0 := by
  rw [delChannel, Finset.sum_congr rfl fun s _ => patternProb_zero s, Finset.sum_ite_eq']
  simp only [mem_filter, mem_univ, true_and, delOutput_false]
  by_cases h : y = List.ofFn x <;> simp [h, eq_comm]

/-- Rate `0` is achievable (one message, never in error), so the set whose supremum
defines `capDel` is nonempty. -/
theorem achievable_zero (d : ℝ) : Achievable d 0 := by
  intro ε hε
  refine ⟨0, fun n _ => ⟨1, by simp, ⟨fun _ _ => false, fun _ => 0⟩, ?_⟩⟩
  simp [avgError, hε.le]

end CryptoLean.OpenProblems.Deletion

#print axioms CryptoLean.OpenProblems.Deletion.vtCode_single_deletion
#print axioms CryptoLean.OpenProblems.Deletion.exists_vtCode_card
#print axioms CryptoLean.OpenProblems.Deletion.exists_vtCode_card_real
#print axioms CryptoLean.OpenProblems.Deletion.sum_patternProb
#print axioms CryptoLean.OpenProblems.Deletion.sum_delChannel
#print axioms CryptoLean.OpenProblems.Deletion.delChannel_zero
#print axioms CryptoLean.OpenProblems.Deletion.achievable_zero
