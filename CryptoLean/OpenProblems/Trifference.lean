import Mathlib

/-!
# The trifference problem: open problem #26

A code `C ⊆ {0,1,2}ⁿ` is *trifferent* (a perfect 3-hash code over a ternary alphabet) if
for every three distinct codewords `x, y, z ∈ C` there is a coordinate `i` at which
`x i, y i, z i` are pairwise distinct. `T n` is the largest size of a trifferent code of
length `n`.

* Open problem #26 (determine the rate `R₃ = limsup (log₂ T n) / n`) is recorded only as a
  `Prop` candidate equality (`TrifferenceRateEqualsKornerMarton`); it is **not** proved
  here and remains open.
* Proved (known results): `T 0 = 1`, `T 1 = 3`, `T 2 = 4`, `T 3 = 6`, `T 4 = 9`;
  monotonicity `T n ≤ T (n+1)`; the elementary recursion `2 T(n+1) ≤ 3 T(n)` for `n ≥ 1`;
  and the elementary upper bound `T n ≤ 2 (3/2)ⁿ` (stated as `2ⁿ T n ≤ 2 · 3ⁿ`).

Note: `T` is *not* supermultiplicative under the naive product code (e.g. `T 1 ^ 2 = 9`
but `T 2 = 4`), so no such statement is made here.
-/

namespace CryptoLean.OpenProblems.Trifference

/-- A ternary code of length `n` is *trifferent* if any three distinct codewords are
separated (take three pairwise distinct values) at some coordinate. -/
def IsTrifferent {n : ℕ} (C : Finset (Fin n → Fin 3)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, x ≠ y → x ≠ z → y ≠ z →
    ∃ i, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i

set_option synthInstance.maxSize 1024 in
instance {n : ℕ} (C : Finset (Fin n → Fin 3)) : Decidable (IsTrifferent C) := by
  unfold IsTrifferent; infer_instance

/-- `T n`: the maximum size of a trifferent code of length `n`. -/
def T (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 3))).filter IsTrifferent).sup Finset.card

/-- The trifference rate `R₃ = limsup_{n → ∞} (log₂ T n) / n`. -/
noncomputable def rate : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (T n) / n) Filter.atTop

/-! ## Open problem statement (unproved) -/

/-- **Open problem #26 (ProofAtlas rank 441): the trifference problem.** Statement
(standard formulation; ProofAtlas text not available offline): "Determine the maximum
size `T(n)` of a trifferent code of length `n` over `{0,1,2}` — equivalently, determine
the rate `R₃ = limsup_{n→∞} (1/n) log₂ T(n)`." Known: `(1/4) log₂(9/5) ≤ R₃ ≤ log₂(3/2)`
(Körner–Marton 1988 lower bound; the elementary upper bound proved below, with small known
improvements below `log₂(3/2)`). The exact value is OPEN.

Modelling: "determine `R₃`" is not itself a proposition, so we record the specific
candidate equality `R₃ = (1/4) log₂(9/5)` (the best known lower bound, Körner–Marton).
This is only one possible answer; it is NOT a known conjecture-turned-theorem, it is
unproved here, and the problem remains open. `rate` uses `Filter.limsup` on `ℝ`. -/
def TrifferenceRateEqualsKornerMarton : Prop :=
  rate = (1 / 4 : ℝ) * Real.logb 2 (9 / 5)

/-! ## Basic facts about `T` -/

theorem card_le_T {n : ℕ} {C : Finset (Fin n → Fin 3)} (hC : IsTrifferent C) :
    C.card ≤ T n :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hC⟩)

theorem T_le_of {n k : ℕ} (h : ∀ C : Finset (Fin n → Fin 3), IsTrifferent C → C.card ≤ k) :
    T n ≤ k :=
  Finset.sup_le fun C hC => h C (Finset.mem_filter.1 hC).2

/-- Codes with at most two words are trivially trifferent. -/
theorem isTrifferent_of_card_le_two {n : ℕ} {C : Finset (Fin n → Fin 3)} (h : C.card ≤ 2) :
    IsTrifferent C := by
  intro x hx y hy z hz hxy hxz hyz
  exfalso
  have : ({x, y, z} : Finset _).card ≤ C.card := Finset.card_le_card (by
    intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption)
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
    Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton] at this
  omega

theorem T_le_pow (n : ℕ) : T n ≤ 3 ^ n :=
  T_le_of fun C _ => by
    simpa [Fintype.card_fun, Fintype.card_fin] using Finset.card_le_univ C

/-- For `n ≥ 1` the three constant words form a trifferent code. -/
theorem three_le_T {n : ℕ} (hn : 1 ≤ n) : 3 ≤ T n := by
  let c : Fin 3 → Fin n → Fin 3 := fun a _ => a
  have hc : Function.Injective c := fun a b h => congrFun h ⟨0, hn⟩
  have : IsTrifferent (Finset.univ.image c) := by
    intro x hx y hy z hz hxy hxz hyz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy hz
    obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; obtain ⟨d, rfl⟩ := hz
    exact ⟨⟨0, hn⟩, fun h => hxy (congrArg c h), fun h => hxz (congrArg c h),
      fun h => hyz (congrArg c h)⟩
  simpa [Finset.card_image_of_injective _ hc] using card_le_T this

/-- **Known result** (folklore; e.g. Körner–Marton, *New bounds for perfect hashing via
information theory*, European J. Combin. 9 (1988)): `T` is nondecreasing — prepend a fixed
symbol to every codeword. -/
theorem T_mono (n : ℕ) : T n ≤ T (n + 1) := by
  apply T_le_of
  intro C hC
  let f : (Fin n → Fin 3) → (Fin (n + 1) → Fin 3) := fun v => Fin.cons (α := fun _ => Fin 3) 0 v
  have hf : Function.Injective f := Fin.cons_right_injective (α := fun _ => Fin 3) 0
  have : IsTrifferent (C.image f) := by
    intro x hx y hy z hz hxy hxz hyz
    simp only [Finset.mem_image] at hx hy hz
    obtain ⟨x, hx, rfl⟩ := hx; obtain ⟨y, hy, rfl⟩ := hy; obtain ⟨z, hz, rfl⟩ := hz
    obtain ⟨i, hi⟩ := hC x hx y hy z hz (fun h => hxy (h ▸ rfl)) (fun h => hxz (h ▸ rfl))
      (fun h => hyz (h ▸ rfl))
    exact ⟨i.succ, by simpa [f] using hi⟩
  simpa [Finset.card_image_of_injective _ hf] using card_le_T this

/-! ## The elementary recursion -/

private theorem fin3_pigeon (a u v w : Fin 3) (hu : u ≠ a) (hv : v ≠ a) (hw : w ≠ a)
    (huv : u ≠ v) (huw : u ≠ w) : v = w := by
  simp only [ne_eq, Fin.ext_iff] at *
  have := a.isLt; have := u.isLt; have := v.isLt; have := w.isLt
  omega

/-- Words of a trifferent code of length `n+1` that avoid the symbol `a` in coordinate `0`
number at most `max 2 (T n)`: if there are at least three, coordinate `0` never separates
them, so their tails are distinct and form a trifferent code of length `n`. -/
theorem card_filter_le {n : ℕ} {C : Finset (Fin (n + 1) → Fin 3)} (hC : IsTrifferent C)
    (a : Fin 3) : (C.filter (fun x => x 0 ≠ a)).card ≤ max 2 (T n) := by
  set S := C.filter (fun x => x 0 ≠ a) with hS
  by_cases h2 : S.card ≤ 2
  · exact le_max_of_le_left h2
  push Not at h2
  have hSC : ∀ x ∈ S, x ∈ C ∧ x 0 ≠ a := fun x hx => Finset.mem_filter.1 hx
  -- coordinate 0 never separates three words of `S`
  have key : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ y → x ≠ z → y ≠ z →
      ∃ j : Fin n, x j.succ ≠ y j.succ ∧ x j.succ ≠ z j.succ ∧ y j.succ ≠ z j.succ := by
    intro x hx y hy z hz hxy hxz hyz
    obtain ⟨i, hi⟩ := hC x (hSC x hx).1 y (hSC y hy).1 z (hSC z hz).1 hxy hxz hyz
    refine Fin.cases (fun h0 => ?_) (fun j hj => ⟨j, hj⟩) i hi
    exact absurd (fin3_pigeon a _ _ _ (hSC x hx).2 (hSC y hy).2 (hSC z hz).2 h0.1 h0.2.1)
      h0.2.2
  have hinj : Set.InjOn (Fin.tail : (Fin (n + 1) → Fin 3) → Fin n → Fin 3) S := by
    intro x hx y hy hxy
    by_contra hne
    obtain ⟨z, hz, hzx, hzy⟩ : ∃ z ∈ S, z ≠ x ∧ z ≠ y := by
      have : 0 < ((S.erase x).erase y).card := by
        have h1 := Finset.pred_card_le_card_erase (s := S.erase x) (a := y)
        have h2' := Finset.pred_card_le_card_erase (s := S) (a := x)
        omega
      obtain ⟨z, hz⟩ := Finset.card_pos.1 this
      simp only [Finset.mem_erase] at hz
      exact ⟨z, hz.2.2, hz.2.1, hz.1⟩
    obtain ⟨j, hj, -⟩ := key x hx y hy z hz hne (Ne.symm hzx) (Ne.symm hzy)
    exact hj (congrFun hxy j)
  have htri : IsTrifferent (S.image Fin.tail) := by
    intro x hx y hy z hz hxy hxz hyz
    simp only [Finset.mem_image] at hx hy hz
    obtain ⟨x, hx, rfl⟩ := hx; obtain ⟨y, hy, rfl⟩ := hy; obtain ⟨z, hz, rfl⟩ := hz
    exact key x hx y hy z hz (fun h => hxy (h ▸ rfl)) (fun h => hxz (h ▸ rfl))
      (fun h => hyz (h ▸ rfl))
  have := card_le_T htri
  rw [Finset.card_image_of_injOn hinj] at this
  exact le_max_of_le_right this

private theorem sum_ne (v : Fin 3) : (∑ a : Fin 3, if v = a then 0 else 1) = 2 := by
  revert v; decide

/-- **Known result** (elementary; see Körner–Marton 1988, and Elias, *Zero error capacity
under list decoding*, IEEE Trans. Inform. Theory 34 (1988)): for a trifferent code `C` of
length `n+1`, `2 |C| ≤ 3 max(2, T n)` (double count the three subcodes avoiding one symbol
in the first coordinate). -/
theorem two_mul_T_succ_le (n : ℕ) : 2 * T (n + 1) ≤ 3 * max 2 (T n) := by
  have hb : T (n + 1) ≤ 3 * max 2 (T n) / 2 := by
    apply T_le_of
    intro C hC
    have hsum : ∑ a : Fin 3, (C.filter (fun x => x 0 ≠ a)).card = 2 * C.card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      simp [sum_ne, mul_comm]
    have hle : ∑ a : Fin 3, (C.filter (fun x => x 0 ≠ a)).card ≤ ∑ _a : Fin 3, max 2 (T n) :=
      Finset.sum_le_sum fun a _ => card_filter_le hC a
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
    omega
  omega

/-- **Known result** (elementary recursion, Körner–Marton 1988): for `n ≥ 1`,
`T(n+1) ≤ (3/2) T(n)`, stated as `2 T(n+1) ≤ 3 T(n)`. -/
theorem two_mul_T_succ_le_three_mul {n : ℕ} (hn : 1 ≤ n) : 2 * T (n + 1) ≤ 3 * T n := by
  have := two_mul_T_succ_le n
  have h3 := three_le_T hn
  rwa [max_eq_right (by omega)] at this

/-- **Known result** (elementary upper bound; Körner–Marton 1988, Elias 1988):
`T n ≤ 2 (3/2)ⁿ`, stated in integers as `2ⁿ T n ≤ 2 · 3ⁿ`. Hence the trifference rate is at
most `log₂(3/2)`. -/
theorem T_le_two_mul_three_halves_pow (n : ℕ) : 2 ^ n * T n ≤ 2 * 3 ^ n := by
  induction n with
  | zero => simpa using (T_le_pow 0).trans (by norm_num)
  | succ n ih =>
    have hrec := two_mul_T_succ_le n
    have h23 : 2 ^ n * 2 ≤ 2 * 3 ^ n := by
      rw [mul_comm]; exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (by norm_num) n)
    have hmax : 2 ^ n * max 2 (T n) ≤ 2 * 3 ^ n := by
      rcases le_total 2 (T n) with h | h
      · rw [max_eq_right h]; exact ih
      · rw [max_eq_left h]; exact h23
    calc 2 ^ (n + 1) * T (n + 1) = 2 ^ n * (2 * T (n + 1)) := by ring
      _ ≤ 2 ^ n * (3 * max 2 (T n)) := Nat.mul_le_mul_left _ hrec
      _ = 3 * (2 ^ n * max 2 (T n)) := by ring
      _ ≤ 3 * (2 * 3 ^ n) := Nat.mul_le_mul_left _ hmax
      _ = 2 * 3 ^ (n + 1) := by ring

/-! ## Small exact values -/

/-- **Known result** (trivial): `T 0 = 1`. -/
theorem T_zero : T 0 = 1 := by
  apply le_antisymm (by simpa using T_le_pow 0)
  have : ({fun _ => 0} : Finset (Fin 0 → Fin 3)).card ≤ T 0 :=
    card_le_T (isTrifferent_of_card_le_two (by simp))
  simpa using this

/-- **Known result** (trivial; Körner–Marton 1988 table): `T 1 = 3`. -/
theorem T_one : T 1 = 3 :=
  le_antisymm (by simpa using T_le_pow 1) (three_le_T le_rfl)

/-- A trifferent code of length 2 with 4 words. -/
def code2 : Finset (Fin 2 → Fin 3) := {![0, 0], ![0, 1], ![1, 2], ![2, 2]}

/-- A trifferent code of length 3 with 6 words. -/
def code3 : Finset (Fin 3 → Fin 3) :=
  {![0, 0, 0], ![0, 1, 1], ![1, 0, 2], ![1, 2, 1], ![2, 1, 2], ![2, 2, 0]}

/-- The ternary tetracode `{(a, b, a+b, a+2b)}`: a trifferent code of length 4 with 9 words. -/
def code4 : Finset (Fin 4 → Fin 3) :=
  {![0, 0, 0, 0], ![0, 1, 1, 2], ![0, 2, 2, 1], ![1, 0, 1, 1], ![1, 1, 2, 0], ![1, 2, 0, 2],
   ![2, 0, 2, 2], ![2, 1, 0, 1], ![2, 2, 1, 0]}

theorem code2_trifferent : IsTrifferent code2 := by decide
theorem code3_trifferent : IsTrifferent code3 := by decide
set_option maxRecDepth 20000 in
theorem code4_trifferent : IsTrifferent code4 := by decide

/-- **Known result** (Körner–Marton 1988 table of small values): `T 2 = 4`. -/
theorem T_two : T 2 = 4 := by
  apply le_antisymm
  · have := two_mul_T_succ_le 1; rw [T_one] at this; norm_num at this; omega
  · have := card_le_T code2_trifferent; rwa [show code2.card = 4 by decide] at this

/-- **Known result** (Körner–Marton 1988 table of small values): `T 3 = 6`. -/
theorem T_three : T 3 = 6 := by
  apply le_antisymm
  · have := two_mul_T_succ_le 2; rw [T_two] at this; norm_num at this; omega
  · have := card_le_T code3_trifferent; rwa [show code3.card = 6 by decide] at this

/-- **Known result** (Körner–Marton 1988 table of small values; the tetracode is optimal):
`T 4 = 9`. -/
theorem T_four : T 4 = 9 := by
  apply le_antisymm
  · have := two_mul_T_succ_le 3; rw [T_three] at this; norm_num at this; omega
  · have := card_le_T code4_trifferent; rwa [show code4.card = 9 by decide] at this

end CryptoLean.OpenProblems.Trifference

#print axioms CryptoLean.OpenProblems.Trifference.T_mono
#print axioms CryptoLean.OpenProblems.Trifference.two_mul_T_succ_le
#print axioms CryptoLean.OpenProblems.Trifference.two_mul_T_succ_le_three_mul
#print axioms CryptoLean.OpenProblems.Trifference.T_le_two_mul_three_halves_pow
#print axioms CryptoLean.OpenProblems.Trifference.T_zero
#print axioms CryptoLean.OpenProblems.Trifference.T_one
#print axioms CryptoLean.OpenProblems.Trifference.T_two
#print axioms CryptoLean.OpenProblems.Trifference.T_three
#print axioms CryptoLean.OpenProblems.Trifference.T_four
