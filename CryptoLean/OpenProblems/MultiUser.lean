import Mathlib

/-!
# Multi-user information theory: open problems #155, #390, #342

All three problems are OPEN. None of them is resolved, or claimed to be resolved, here. Each
is recorded only as an unproved `def … : Prop`; the proved theorems are standard known facts
about the models, included to show the definitions are non-vacuous.

## Common infrastructure

* `StochKernel α β`: a finite-output stochastic kernel (a map `α → β → ℝ` into probability
  vectors). This is the same data as Mathlib's (now deprecated) `stdSimplex ℝ β`; Mathlib's
  replacement `StdSimplex` is `Finsupp`-based and its measure-theoretic
  `ProbabilityTheory.Kernel` is far heavier than finite alphabets need, so we keep the plain
  probability-vector form.
* `causalLaw K u z = ∏ᵢ K(u i z)(z i)`: the law of an output sequence `z` of `n` channel uses
  when the input at time `i` is `u i z`, a **strictly causal** function of `z` (it may only
  read `z j` for `j < i`, `StrictlyCausal`). Known fact (chain rule): it is a probability
  distribution, `sum_causalLaw`.
* Known fact (counting converse, the elementary cardinality bound `C ≤ log₂ |Y|`; cf.
  Cover–Thomas, *Elements of Information Theory*, Ch. 7; El Gamal–Kim, *Network Information
  Theory*, Ch. 3): a decoder that sees only a projection `proj ∘ z` with values in `B` has total
  success `∑ₘ P(correct | m) ≤ |B|ⁿ` (`sum_success_le`).

## #155 (relay channel)

`RelayCode`: encoder, strictly causal relay functions `xᵣ,ᵢ = rᵢ(y_{r,1..i-1})`, decoder;
`relayErrorProb` is the average error probability; `RelayAchievable`, `relayCapacity`.
Proved (known): `0 ≤ C`, rate `0` is achievable, every achievable rate is `≤ log₂ |Y|`, hence
`C ≤ log₂ |Y|` (`relayCapacity_le_logb_card`). The open problem is the `Prop`
`RelayCapacityComputable`.

## #390 (3-receiver broadcast channel)

`BCCode`, `bcErrorProb`, `BCAchievable`, `bcCapacityRegion` (closure of achievable triples).
Proved (known): `(0,0,0)` is in the region, and every achievable triple has
`Rⱼ ≤ log₂ |Yⱼ|` (`bcAchievable_le`). The open problem is the `Prop`
`BCCapacityRegionComputable`.

## #342 (Li–Li undirected multiple-unicast conjecture)

`Network` (finite multigraph with edge capacities, a per-direction usability flag, unicast
sessions), `NCode` (zero-error causal network code over `rounds` rounds and a block of length
`n`), `codingRegion`, `Routing` (fractional path routing), `routingRegion`.
The open problem is the `Prop` `LiLiConjecture` (undirected networks).
Proved (known, Ahlswede–Cai–Li–Yeung 2000): in the **directed** two-unicast butterfly network
with unit capacities, network coding achieves the rate pair `(1,1)`, while every fractional
routing satisfies `r₀ + r₁ ≤ 1`, so `(1,1)` is not even in the closure of the routing region
(`butterfly_coding_gain`). This is a DIRECTED network; it says nothing about the undirected
Li–Li conjecture.
-/

namespace CryptoLean.OpenProblems.MultiUser

open Finset Real

set_option linter.unusedSectionVars false

/-! ## Part 0: stochastic kernels, causal laws, the counting converse -/

/-- A stochastic kernel from `α` to a finite set `β`: each row is a probability vector. -/
structure StochKernel (α β : Type*) [Fintype β] where
  /-- `p a b` = probability of output `b` on input `a`. -/
  p : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ p a b
  sum_eq_one : ∀ a, ∑ b, p a b = 1

/-- `u i y` only depends on the coordinates `y j` with `j < i` (strict causality). -/
def StrictlyCausal {n : ℕ} {β γ : Type*} (u : Fin n → (Fin n → β) → γ) : Prop :=
  ∀ i y y', (∀ j, j < i → y j = y' j) → u i y = u i y'

/-- Law of the output sequence `z` of `n` uses of a memoryless channel `K` when the input at
time `i` is `u i z` (a strictly causal function of past outputs). -/
def causalLaw {α β : Type*} [Fintype β] (K : StochKernel α β) {n : ℕ}
    (u : Fin n → (Fin n → β) → α) (z : Fin n → β) : ℝ :=
  ∏ i, K.p (u i z) (z i)

theorem causalLaw_nonneg {α β : Type*} [Fintype β] (K : StochKernel α β) {n : ℕ}
    (u : Fin n → (Fin n → β) → α) (z : Fin n → β) : 0 ≤ causalLaw K u z :=
  Finset.prod_nonneg fun _ _ => K.nonneg _ _

private theorem snoc_eq_of_lt {β : Type*} {n : ℕ} {y y' : Fin n → β} {a a' : β}
    {m : Fin (n + 1)} (h : ∀ j : Fin n, j.castSucc < m → y j = y' j) :
    ∀ k, k < m → Fin.snoc (α := fun _ => β) y a k = Fin.snoc (α := fun _ => β) y' a' k := by
  intro k hk
  have hk' : (k : ℕ) < n := by have := m.isLt; have : (k : ℕ) < m := hk; omega
  obtain ⟨j, rfl⟩ : ∃ j : Fin n, j.castSucc = k := ⟨k.castLT hk', Fin.castSucc_castLT _ _⟩
  simp only [Fin.snoc_castSucc]
  exact h j hk

/-- Known fact (chain rule for strictly causal channel use): `causalLaw` is a probability
distribution on output sequences. -/
theorem sum_causalLaw {α β : Type*} [Fintype β] [Nonempty β] (K : StochKernel α β) :
    ∀ {n : ℕ} (u : Fin n → (Fin n → β) → α), StrictlyCausal u →
      ∑ z, causalLaw K u z = 1 := by
  intro n
  induction n with
  | zero => intro u _; simp [causalLaw]
  | succ n ih =>
    intro u hu
    obtain ⟨b₀⟩ := ‹Nonempty β›
    set u' : Fin n → (Fin n → β) → α := fun i y => u i.castSucc (Fin.snoc y b₀) with hu'
    have hc' : StrictlyCausal u' := by
      intro _i y y' h
      simp only [hu']
      apply hu
      exact snoc_eq_of_lt (fun j hj => h j (by simpa using hj))
    have key : ∀ (z' : Fin n → β) (a : β),
        causalLaw K u (Fin.snoc (α := fun _ => β) z' a) =
          causalLaw K u' z' * K.p (u (Fin.last n) (Fin.snoc (α := fun _ => β) z' b₀)) a := by
      intro z' a
      simp only [causalLaw, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
      congr 1
      · refine Finset.prod_congr rfl fun i _ => ?_
        congr 1
        exact hu _ _ _ (snoc_eq_of_lt (fun j _ => rfl))
      · congr 1
        exact hu _ _ _ (snoc_eq_of_lt (fun j _ => rfl))
    rw [← (Fin.snocEquiv (fun _ => β)).sum_comp, Fintype.sum_prod_type_right]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, key, ← Finset.mul_sum, K.sum_eq_one, mul_one]
    exact ih u' hc'

/-- Known fact (counting converse): if the decoder only sees `proj ∘ z` (values in `B`), the
total success probability over all `M` messages is at most `|B|ⁿ`. -/
theorem sum_success_le {α β B : Type*} [Fintype β] [Nonempty β] [Fintype B] [DecidableEq B]
    (K : StochKernel α β) (proj : β → B) {n M : ℕ} (u : Fin M → Fin n → (Fin n → β) → α)
    (hu : ∀ m, StrictlyCausal (u m)) (g : (Fin n → B) → Fin M) :
    ∑ m, ∑ z, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 1 else 0)
      ≤ (Fintype.card B : ℝ) ^ n := by
  classical
  rw [Finset.sum_comm]
  have h1 : ∀ z : Fin n → β, ∑ m, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 1 else 0)
      = causalLaw K (u (g (fun i => proj (z i)))) z := by
    intro z
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]; simp
  simp only [h1]
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun z : Fin n → β => fun i => proj (z i))]
  calc ∑ y : Fin n → B, ∑ z ∈ univ.filter (fun z : Fin n → β => (fun i => proj (z i)) = y),
          causalLaw K (u (g (fun i => proj (z i)))) z
      = ∑ y : Fin n → B, ∑ z ∈ univ.filter (fun z : Fin n → β => (fun i => proj (z i)) = y),
          causalLaw K (u (g y)) z := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z hz => ?_
        rw [(Finset.mem_filter.1 hz).2]
    _ ≤ ∑ _y : Fin n → B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← sum_causalLaw K (u (g y)) (hu _)]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun z _ _ => causalLaw_nonneg K _ z)
    _ = (Fintype.card B : ℝ) ^ n := by simp

/-- Error probability with decoder `g` reading `proj ∘ z`, averaged uniformly over messages. -/
noncomputable def projErrorProb {α β B : Type*} [Fintype β] [DecidableEq B] (K : StochKernel α β)
    (proj : β → B) {n M : ℕ} (u : Fin M → Fin n → (Fin n → β) → α) (g : (Fin n → B) → Fin M) : ℝ :=
  (M : ℝ)⁻¹ * ∑ m, ∑ z, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 0 else 1)

/-- Known fact (counting converse, error form): `M · (1 - Pₑ) ≤ |B|ⁿ`. -/
theorem card_mul_one_sub_projErrorProb_le {α β B : Type*} [Fintype β] [Nonempty β] [Fintype B]
    [DecidableEq B] (K : StochKernel α β) (proj : β → B) {n M : ℕ}
    (u : Fin M → Fin n → (Fin n → β) → α) (hu : ∀ m, StrictlyCausal (u m))
    (g : (Fin n → B) → Fin M) :
    (M : ℝ) * (1 - projErrorProb K proj u g) ≤ (Fintype.card B : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hsplit : ∀ m, ∑ z, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 0 else 1)
      = 1 - ∑ z, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 1 else 0) := by
    intro m
    have h1 := sum_causalLaw K (u m) (hu m)
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun z _ => ?_) h1
    split_ifs <;> ring
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have : (M : ℝ) * (1 - projErrorProb K proj u g) =
      ∑ m, ∑ z, causalLaw K (u m) z * (if g (fun i => proj (z i)) = m then 1 else 0) := by
    simp only [projErrorProb, hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring
  rw [this]
  exact sum_success_le K proj u hu g

/-- Elementary rate lemma: if `2^{nR} ≤ 2 · Cⁿ` for arbitrarily large `n`, then
`R ≤ log₂ C`. -/
theorem le_logb_of_rpow_le {R C : ℝ} (hC : 1 ≤ C)
    (h : ∀ N : ℕ, ∃ n ≥ N, (2 : ℝ) ^ ((n : ℝ) * R) ≤ 2 * C ^ n) : R ≤ logb 2 C := by
  by_contra hlt'
  have hlt := not_le.1 hlt'
  set L := logb 2 C
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (R - L))
  obtain ⟨n, hn, hle⟩ := h N
  have hCpos : 0 < C := by linarith
  have hCL : C ^ n = (2 : ℝ) ^ ((n : ℝ) * L) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hCpos,
      Real.rpow_natCast]
  rw [hCL, show (2 : ℝ) * 2 ^ ((n : ℝ) * L) = 2 ^ (1 + (n : ℝ) * L) by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]] at hle
  rw [Real.rpow_le_rpow_left_iff (by norm_num)] at hle
  have hRL : 0 < R - L := by linarith
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 < (n : ℝ) * (R - L) := by
    have := (div_lt_iff₀ hRL).1 (lt_of_lt_of_le hN hn')
    linarith
  nlinarith


/-- Known fact (counting converse with side messages): messages `(m, k)`, decoder recovers `m`
only, from `proj ∘ z`. Then the total success is at most `|κ| · |B|ⁿ`. -/
theorem sum_success_prod_le {α β B κ : Type*} [Fintype β] [Nonempty β] [Fintype B]
    [DecidableEq B] [Fintype κ] (K : StochKernel α β) (proj : β → B) {n M : ℕ}
    (u : Fin M → κ → Fin n → (Fin n → β) → α) (hu : ∀ m k, StrictlyCausal (u m k))
    (g : (Fin n → B) → Fin M) :
    ∑ m, ∑ k, ∑ z, causalLaw K (u m k) z * (if g (fun i => proj (z i)) = m then 1 else 0)
      ≤ (Fintype.card κ : ℝ) * (Fintype.card B : ℝ) ^ n := by
  rw [Finset.sum_comm]
  calc _ ≤ ∑ _k : κ, (Fintype.card B : ℝ) ^ n :=
        Finset.sum_le_sum fun k _ => sum_success_le K proj (fun m => u m k) (fun m => hu m k) g
    _ = _ := by simp

/-- `|ι| · (1 - average error) = total success`, for any family of probability laws. -/
theorem card_mul_one_sub_avg {ι Z : Type*} [Fintype ι] [Fintype Z] (P : ι → Z → ℝ)
    (hP : ∀ m, ∑ z, P m z = 1) (ok : ι → Z → Prop) [∀ m z, Decidable (ok m z)]
    (hι : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * (1 - (Fintype.card ι : ℝ)⁻¹ *
        ∑ m, ∑ z, P m z * (if ok m z then 0 else 1)) =
      ∑ m, ∑ z, P m z * (if ok m z then 1 else 0) := by
  have hsplit : ∀ m, ∑ z, P m z * (if ok m z then 0 else 1)
      = 1 - ∑ z, P m z * (if ok m z then 1 else 0) := by
    intro m
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun z _ => ?_) (hP m)
    split_ifs <;> ring
  have hpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hι
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one]
  field_simp
  ring

/-- Elementary step: from `Mⱼ K (1 - Pₑ) ≤ K Cⁿ` and `Pₑ ≤ 1/2` get `Mⱼ ≤ 2 Cⁿ`. -/
theorem le_two_mul_of_mul_one_sub_le {Mj K Pe D : ℝ} (hK : 0 < K) (hMj : 0 ≤ Mj)
    (hPe : Pe ≤ 1 / 2) (h : Mj * K * (1 - Pe) ≤ K * D) : Mj ≤ 2 * D := by
  have h1 : Mj * K * (1 / 2) ≤ Mj * K * (1 - Pe) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : K * (Mj / 2) ≤ K * D := by nlinarith
  have := le_of_mul_le_mul_left h2 hK
  linarith

/-! ## Part 1: problem #155, the discrete memoryless relay channel -/

section Relay

variable {X Xr Y Yr : Type*} [Fintype Y] [Fintype Yr] [DecidableEq Y]

/-- A finite-alphabet discrete memoryless relay channel `p(y, y_r | x, x_r)`. -/
abbrev RelayChannel (X Xr Y Yr : Type*) [Fintype Y] [Fintype Yr] :=
  StochKernel (X × Xr) (Y × Yr)

/-- An `(M, n)` relay code: encoder, strictly causal relay functions
`x_{r,i} = r_i(y_{r,1}, …, y_{r,i-1})`, and a decoder at the destination. -/
structure RelayCode (X Xr Y Yr : Type*) (M n : ℕ) where
  enc : Fin M → Fin n → X
  relay : Fin n → (Fin n → Yr) → Xr
  relay_causal : StrictlyCausal relay
  dec : (Fin n → Y) → Fin M

/-- Channel inputs at time `i` for message `m`, as a function of the output sequence. -/
def RelayCode.inputs {M n : ℕ} (c : RelayCode X Xr Y Yr M n) (m : Fin M) :
    Fin n → (Fin n → Y × Yr) → X × Xr :=
  fun i z => (c.enc m i, c.relay i (fun j => (z j).2))

theorem RelayCode.inputs_causal {M n : ℕ} (c : RelayCode X Xr Y Yr M n) (m : Fin M) :
    StrictlyCausal (c.inputs m) := by
  intro i y y' h
  simp only [RelayCode.inputs]
  rw [c.relay_causal i _ _ (fun j hj => by rw [h j hj])]

/-- Average (over uniformly distributed messages) error probability of a relay code. -/
noncomputable def relayErrorProb (W : RelayChannel X Xr Y Yr) {M n : ℕ}
    (c : RelayCode X Xr Y Yr M n) : ℝ :=
  projErrorProb W Prod.fst c.inputs c.dec

/-- `R ≥ 0` is achievable: for every `ε > 0` and all large `n` there is an `(M, n)` code with
`M ≥ 2^{nR}` and average error at most `ε`. -/
def RelayAchievable (W : RelayChannel X Xr Y Yr) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ M : ℕ, (2 : ℝ) ^ ((n : ℝ) * R) ≤ M ∧
    ∃ c : RelayCode X Xr Y Yr M n, relayErrorProb W c ≤ ε

/-- Average-error Shannon capacity of the relay channel (bits per channel use). -/
noncomputable def relayCapacity (W : RelayChannel X Xr Y Yr) : ℝ :=
  sSup {R | RelayAchievable W R}

/-- Known (trivial) fact: the capacity is nonnegative. -/
theorem relayCapacity_nonneg (W : RelayChannel X Xr Y Yr) : 0 ≤ relayCapacity W :=
  Real.sSup_nonneg fun _ h => h.1

/-- Known (trivial) fact: rate `0` is achievable (one message, zero error) when the input
alphabets are nonempty. -/
theorem relayAchievable_zero [Nonempty X] [Nonempty Xr] (W : RelayChannel X Xr Y Yr) :
    RelayAchievable W 0 := by
  refine ⟨le_rfl, fun ε hε => ⟨0, fun n _ => ⟨1, by simp, ?_⟩⟩⟩
  refine ⟨⟨fun _ _ => Classical.arbitrary X, fun _ _ => Classical.arbitrary Xr,
    fun _ _ _ _ => rfl, fun _ => 0⟩, ?_⟩
  have : relayErrorProb W (⟨fun _ _ => Classical.arbitrary X, fun _ _ => Classical.arbitrary Xr,
      fun _ _ _ _ => rfl, fun _ => 0⟩ : RelayCode X Xr Y Yr 1 n) = 0 := by
    simp [relayErrorProb, projErrorProb, Subsingleton.elim _ (0 : Fin 1)]
  rw [this]; exact hε.le

/-- Known result (cardinality converse; cf. El Gamal–Kim, *Network Information Theory*,
Ch. 16): every achievable rate of a relay channel is at most `log₂ |Y|`. -/
theorem relayAchievable_le_logb_card [Nonempty Y] [Nonempty Yr] (W : RelayChannel X Xr Y Yr)
    {R : ℝ} (hR : RelayAchievable W R) : R ≤ logb 2 (Fintype.card Y) := by
  have hY : (1 : ℝ) ≤ Fintype.card Y := by exact_mod_cast Fintype.card_pos
  obtain ⟨N, hN⟩ := hR.2 (1 / 2) (by norm_num)
  refine le_logb_of_rpow_le hY fun N' => ⟨max N N', le_max_right _ _, ?_⟩
  obtain ⟨M, hM, c, hc⟩ := hN (max N N') (le_max_left _ _)
  have h := card_mul_one_sub_projErrorProb_le W Prod.fst c.inputs c.inputs_causal c.dec
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have : (M : ℝ) * (1 / 2) ≤ M * (1 - relayErrorProb W c) :=
    mul_le_mul_of_nonneg_left (by linarith) hM0
  unfold relayErrorProb at this
  linarith

/-- Known result: `C ≤ log₂ |Y|` for every relay channel (with nonempty output alphabets). -/
theorem relayCapacity_le_logb_card [Nonempty Y] [Nonempty Yr] (W : RelayChannel X Xr Y Yr) :
    relayCapacity W ≤ logb 2 (Fintype.card Y) := by
  refine Real.sSup_le (fun R hR => relayAchievable_le_logb_card W hR) ?_
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast Fintype.card_pos)

/-- Relay channel with alphabets `Fin a, Fin b, Fin c, Fin d` given by a rational table. -/
def IsStochasticTable {a b c d : ℕ} (q : Fin a → Fin b → Fin c → Fin d → ℚ) : Prop :=
  (∀ x xr y yr, 0 ≤ q x xr y yr) ∧ ∀ x xr, ∑ y, ∑ yr, q x xr y yr = 1

/-- The real relay channel defined by a rational stochastic table. -/
noncomputable def relayOfTable {a b c d : ℕ} (q : Fin a → Fin b → Fin c → Fin d → ℚ)
    (hq : IsStochasticTable q) : RelayChannel (Fin a) (Fin b) (Fin c) (Fin d) where
  p xx yy := (q xx.1 xx.2 yy.1 yy.2 : ℝ)
  nonneg xx yy := by exact_mod_cast hq.1 _ _ _ _
  sum_eq_one xx := by
    rw [Fintype.sum_prod_type]
    exact_mod_cast hq.2 xx.1 xx.2

/-- Finite encoding of a four-index rational table (nested lists, `x`-major). -/
def encodeTable {a b c d : ℕ} (q : Fin a → Fin b → Fin c → Fin d → ℚ) :
    List (List (List (List ℚ))) :=
  List.ofFn fun x => List.ofFn fun xr => List.ofFn fun y => List.ofFn fun yr => q x xr y yr

/-- **Open problem #155 (ProofAtlas, edition 2026-11-12): capacity of the general discrete
memoryless relay channel.** Exact statement: "Find a computable exact average-error
Shannon-capacity characterization for every finite-alphabet discrete memoryless relay channel
with law p(y,y_r|x,x_r), where the relay input at time i depends only on its observations
before time i." Status: OPEN (a proposed formula by Ponniah was refuted by Shiu's
counterexample). This `Prop` is NOT proved.

Modelling and simplifications (all deliberate):
* "Computable characterization" is formalized as **uniform computability of the capacity
  as a real number**: a Mathlib-`Computable` map `F` that, given the finite encoding of the
  channel law (`encodeTable`) and a precision `k`, returns a rational within `2^{-k}` of
  `relayCapacity`. A single-letter formula with computable optimization (e.g. a max of mutual
  informations over finitely many bounded-cardinality distributions) would yield such an `F`;
  the converse is not claimed, so this `Prop` is a necessary consequence of — not literally the
  same as — an "exact characterization" in the informal sense, which has no standard formal
  definition.
* Channel laws are restricted to **rational** entries (as an algorithm needs a finite input);
  the capacity itself is the true real-valued capacity of the real channel.
* Capacity is the operational average-error capacity: `sSup` of rates `R ≥ 0` such that for
  every `ε > 0` and all large `n` an `(⌈2^{nR}⌉, n)` code with average error `≤ ε` exists; the
  relay is strictly causal (`relay_causal`), messages are uniform, decoding at `Y` only.
* No deterministic/stochastic encoder distinction: encoders, relay maps and decoder are
  deterministic, as is standard (randomization does not change average-error capacity). -/
def RelayCapacityComputable : Prop :=
  ∃ F : List (List (List (List ℚ))) × ℕ → ℚ, Computable F ∧
    ∀ (a b c d : ℕ) (q : Fin a → Fin b → Fin c → Fin d → ℚ) (hq : IsStochasticTable q) (k : ℕ),
      |(F (encodeTable q, k) : ℝ) - relayCapacity (relayOfTable q hq)| ≤ (1 / 2 : ℝ) ^ k

end Relay

/-! ## Part 2: problem #390, the 3-receiver discrete memoryless broadcast channel -/

section Broadcast

variable {X Y₁ Y₂ Y₃ : Type*} [Fintype Y₁] [Fintype Y₂] [Fintype Y₃]
  [DecidableEq Y₁] [DecidableEq Y₂] [DecidableEq Y₃]

/-- A 3-receiver discrete memoryless broadcast channel `p(y₁, y₂, y₃ | x)`. -/
abbrev BroadcastChannel (X Y₁ Y₂ Y₃ : Type*) [Fintype Y₁] [Fintype Y₂] [Fintype Y₃] :=
  StochKernel X (Y₁ × Y₂ × Y₃)

/-- An `(M₁, M₂, M₃, n)` broadcast code with private messages. -/
structure BCCode (X Y₁ Y₂ Y₃ : Type*) (M₁ M₂ M₃ n : ℕ) where
  enc : Fin M₁ × Fin M₂ × Fin M₃ → Fin n → X
  dec₁ : (Fin n → Y₁) → Fin M₁
  dec₂ : (Fin n → Y₂) → Fin M₂
  dec₃ : (Fin n → Y₃) → Fin M₃

/-- All three receivers decode correctly. -/
def bcOk {M₁ M₂ M₃ n : ℕ} (c : BCCode X Y₁ Y₂ Y₃ M₁ M₂ M₃ n) (m : Fin M₁ × Fin M₂ × Fin M₃)
    (z : Fin n → Y₁ × Y₂ × Y₃) : Prop :=
  c.dec₁ (fun i => (z i).1) = m.1 ∧ c.dec₂ (fun i => (z i).2.1) = m.2.1 ∧
    c.dec₃ (fun i => (z i).2.2) = m.2.2

instance {M₁ M₂ M₃ n : ℕ} (c : BCCode X Y₁ Y₂ Y₃ M₁ M₂ M₃ n) m z : Decidable (bcOk c m z) := by
  unfold bcOk; infer_instance

/-- Average probability that some receiver decodes wrongly (uniform messages). -/
noncomputable def bcErrorProb (W : BroadcastChannel X Y₁ Y₂ Y₃) {M₁ M₂ M₃ n : ℕ}
    (c : BCCode X Y₁ Y₂ Y₃ M₁ M₂ M₃ n) : ℝ :=
  (Fintype.card (Fin M₁ × Fin M₂ × Fin M₃) : ℝ)⁻¹ *
    ∑ m, ∑ z, causalLaw W (fun i _ => c.enc m i) z * (if bcOk c m z then 0 else 1)

/-- A rate triple is achievable (with vanishing average error). -/
def BCAchievable (W : BroadcastChannel X Y₁ Y₂ Y₃) (R : ℝ × ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2.1 ∧ 0 ≤ R.2.2 ∧ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ M₁ M₂ M₃ : ℕ,
    (2 : ℝ) ^ ((n : ℝ) * R.1) ≤ M₁ ∧ (2 : ℝ) ^ ((n : ℝ) * R.2.1) ≤ M₂ ∧
    (2 : ℝ) ^ ((n : ℝ) * R.2.2) ≤ M₃ ∧
    ∃ c : BCCode X Y₁ Y₂ Y₃ M₁ M₂ M₃ n, bcErrorProb W c ≤ ε

/-- The capacity region: closure of the set of achievable rate triples. -/
def bcCapacityRegion (W : BroadcastChannel X Y₁ Y₂ Y₃) : Set (ℝ × ℝ × ℝ) :=
  closure {R | BCAchievable W R}

/-- Known (trivial) fact: the zero triple is achievable (single messages, zero error). -/
theorem bcAchievable_zero [Nonempty X] (W : BroadcastChannel X Y₁ Y₂ Y₃) :
    BCAchievable W (0, 0, 0) := by
  refine ⟨le_rfl, le_rfl, le_rfl, fun ε hε => ⟨0, fun n _ => ⟨1, 1, 1, by simp, by simp,
    by simp, ⟨fun _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0, fun _ => 0⟩, ?_⟩⟩⟩
  have : bcErrorProb W (⟨fun _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0,
      fun _ => 0⟩ : BCCode X Y₁ Y₂ Y₃ 1 1 1 n) = 0 := by
    have hok : ∀ m z, bcOk (⟨fun _ _ => Classical.arbitrary X, fun _ => 0, fun _ => 0,
        fun _ => 0⟩ : BCCode X Y₁ Y₂ Y₃ 1 1 1 n) m z :=
      fun _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    simp [bcErrorProb, hok]
  rw [this]; exact hε.le

theorem zero_mem_bcCapacityRegion [Nonempty X] (W : BroadcastChannel X Y₁ Y₂ Y₃) :
    ((0 : ℝ), (0 : ℝ), (0 : ℝ)) ∈ bcCapacityRegion W :=
  subset_closure (bcAchievable_zero W)


/-- Counting converse for one receiver of a broadcast code: with the message triple reindexed
as `(mⱼ, rest)` by `e`, and `g` the receiver's decoder, `|M| (1 - Pₑ) ≤ |rest| · |Bⱼ|ⁿ`. -/
theorem bc_receiver_bound [Nonempty Y₁] [Nonempty Y₂] [Nonempty Y₃]
    (W : BroadcastChannel X Y₁ Y₂ Y₃) {M₁ M₂ M₃ n Mj : ℕ} (c : BCCode X Y₁ Y₂ Y₃ M₁ M₂ M₃ n)
    {κ B : Type*} [Fintype κ] [Fintype B] [DecidableEq B]
    (e : Fin Mj × κ ≃ Fin M₁ × Fin M₂ × Fin M₃) (proj : Y₁ × Y₂ × Y₃ → B)
    (g : (Fin n → B) → Fin Mj)
    (hok : ∀ p z, bcOk c (e p) z → g (fun i => proj (z i)) = p.1)
    (hM : 0 < Fintype.card (Fin M₁ × Fin M₂ × Fin M₃)) :
    (Fintype.card (Fin M₁ × Fin M₂ × Fin M₃) : ℝ) * (1 - bcErrorProb W c)
      ≤ (Fintype.card κ : ℝ) * (Fintype.card B : ℝ) ^ n := by
  unfold bcErrorProb
  rw [card_mul_one_sub_avg _ (fun m => sum_causalLaw W _ (fun _ _ _ _ => rfl)) _ hM]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine le_trans ?_ (sum_success_prod_le W proj (fun m k i _ => c.enc (e (m, k)) i)
    (fun _ _ _ _ _ _ => rfl) g)
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ =>
    Finset.sum_le_sum fun z _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (causalLaw_nonneg W _ z)
  by_cases h : bcOk c (e (m, k)) z
  · simp [h, hok (m, k) z h]
  · simp only [h, ite_false]; split_ifs <;> norm_num

/-- Known result (cardinality converse for broadcast channels; cf. El Gamal–Kim,
*Network Information Theory*, Ch. 5): every achievable rate triple satisfies
`Rⱼ ≤ log₂ |Yⱼ|` for each receiver `j`. -/
theorem bcAchievable_le [Nonempty Y₁] [Nonempty Y₂] [Nonempty Y₃]
    (W : BroadcastChannel X Y₁ Y₂ Y₃) {R : ℝ × ℝ × ℝ} (hR : BCAchievable W R) :
    R.1 ≤ logb 2 (Fintype.card Y₁) ∧ R.2.1 ≤ logb 2 (Fintype.card Y₂) ∧
      R.2.2 ≤ logb 2 (Fintype.card Y₃) := by
  obtain ⟨-, -, -, hR⟩ := hR
  obtain ⟨N, hN⟩ := hR (1 / 2) (by norm_num)
  have hpos : ∀ (n : ℕ) (x : ℝ) (M : ℕ), (2 : ℝ) ^ ((n : ℝ) * x) ≤ M → 0 < M := fun n x M h => by
    have : (0 : ℝ) < M := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) h
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · refine le_logb_of_rpow_le (by exact_mod_cast Fintype.card_pos) fun N' =>
      ⟨max N N', le_max_right _ _, ?_⟩
    obtain ⟨M₁, M₂, M₃, h₁, h₂, h₃, c, hc⟩ := hN (max N N') (le_max_left _ _)
    have hM := hpos _ _ _ h₁; have hM2 := hpos _ _ _ h₂; have hM3 := hpos _ _ _ h₃
    have hb := bc_receiver_bound W c (Mj := M₁) (κ := Fin M₂ × Fin M₃) (Equiv.refl _)
      (fun t => t.1) c.dec₁ (fun p z h => h.1) (by simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hM (Nat.mul_pos hM2 hM3))
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hb
    refine le_trans h₁ (le_two_mul_of_mul_one_sub_le (K := (M₂ : ℝ) * M₃) (by positivity)
      (by positivity) hc ?_)
    linarith [hb]
  · refine le_logb_of_rpow_le (by exact_mod_cast Fintype.card_pos) fun N' =>
      ⟨max N N', le_max_right _ _, ?_⟩
    obtain ⟨M₁, M₂, M₃, h₁, h₂, h₃, c, hc⟩ := hN (max N N') (le_max_left _ _)
    have hM := hpos _ _ _ h₁; have hM2 := hpos _ _ _ h₂; have hM3 := hpos _ _ _ h₃
    let e : Fin M₂ × (Fin M₁ × Fin M₃) ≃ Fin M₁ × Fin M₂ × Fin M₃ :=
      { toFun := fun p => (p.2.1, p.1, p.2.2), invFun := fun q => (q.2.1, q.1, q.2.2),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have hb := bc_receiver_bound W c e (fun t => t.2.1) c.dec₂ (fun p z h => h.2.1)
      (by simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hM (Nat.mul_pos hM2 hM3))
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hb
    refine le_trans h₂ (le_two_mul_of_mul_one_sub_le (K := (M₁ : ℝ) * M₃) (by positivity)
      (by positivity) hc ?_)
    linarith [hb]
  · refine le_logb_of_rpow_le (by exact_mod_cast Fintype.card_pos) fun N' =>
      ⟨max N N', le_max_right _ _, ?_⟩
    obtain ⟨M₁, M₂, M₃, h₁, h₂, h₃, c, hc⟩ := hN (max N N') (le_max_left _ _)
    have hM := hpos _ _ _ h₁; have hM2 := hpos _ _ _ h₂; have hM3 := hpos _ _ _ h₃
    let e : Fin M₃ × (Fin M₁ × Fin M₂) ≃ Fin M₁ × Fin M₂ × Fin M₃ :=
      { toFun := fun p => (p.2.1, p.2.2, p.1), invFun := fun q => (q.2.2, q.1, q.2.1),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have hb := bc_receiver_bound W c e (fun t => t.2.2) c.dec₃ (fun p z h => h.2.2)
      (by simp only [Fintype.card_prod, Fintype.card_fin]; exact Nat.mul_pos hM (Nat.mul_pos hM2 hM3))
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hb
    refine le_trans h₃ (le_two_mul_of_mul_one_sub_le (K := (M₁ : ℝ) * M₂) (by positivity)
      (by positivity) hc ?_)
    linarith [hb]

/-- Finite encoding of a broadcast channel table `q x y₁ y₂ y₃`. -/
def IsStochasticBCTable {a b c d : ℕ} (q : Fin a → Fin b → Fin c → Fin d → ℚ) : Prop :=
  (∀ x y₁ y₂ y₃, 0 ≤ q x y₁ y₂ y₃) ∧ ∀ x, ∑ y₁, ∑ y₂, ∑ y₃, q x y₁ y₂ y₃ = 1

/-- The real broadcast channel defined by a rational stochastic table. -/
noncomputable def bcOfTable {a b c d : ℕ} (q : Fin a → Fin b → Fin c → Fin d → ℚ)
    (hq : IsStochasticBCTable q) : BroadcastChannel (Fin a) (Fin b) (Fin c) (Fin d) where
  p x yy := (q x yy.1 yy.2.1 yy.2.2 : ℝ)
  nonneg x yy := by exact_mod_cast hq.1 _ _ _ _
  sum_eq_one x := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    exact_mod_cast hq.2 x

/-- **Open problem #390 (ProofAtlas, edition 2026-11-12): capacity region of general
3-receiver DM broadcast channels.** Exact statement: "Find a computable single-letter
characterization of the capacity region for general 3-receiver discrete memoryless broadcast
channels without degradedness assumptions." Status: OPEN. This `Prop` is NOT proved.

Modelling and simplifications (all deliberate):
* "Computable characterization" is formalized as **uniform computability of the region as a
  closed subset of `ℝ³`** (sup metric): a Mathlib-`Computable` map that, given the encoded
  channel table, a rational point `r` and a precision `k`, returns a rational within `2^{-k}`
  of the distance `infDist r C(W)`. This is the standard notion of a computable closed set.
  The "single-letter" requirement has no standard formal definition and is not modelled; a
  single-letter description with bounded auxiliary cardinalities would give such a map, but
  the converse is not claimed.
* Private messages only (no common message), uniform messages, average error probability
  that *some* receiver errs; capacity region = closure of achievable triples.
* Rational channel tables only (finite algorithmic input). -/
def BCCapacityRegionComputable : Prop :=
  ∃ F : (List (List (List (List ℚ))) × (ℚ × ℚ × ℚ)) × ℕ → ℚ, Computable F ∧
    ∀ (a b c d : ℕ) (q : Fin a → Fin b → Fin c → Fin d → ℚ) (hq : IsStochasticBCTable q)
      (r : ℚ × ℚ × ℚ) (k : ℕ),
      |(F ((encodeTable q, r), k) : ℝ) -
          Metric.infDist ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2 : ℝ)) (bcCapacityRegion (bcOfTable q hq))|
        ≤ (1 / 2 : ℝ) ^ k

end Broadcast

/-! ## Part 3: problem #342, undirected multiple-unicast network coding (Li–Li) -/

section Network

/-- A finite network: `nV` nodes, `nE` edges (a multigraph; edge `e` joins `(ends e).1` and
`(ends e).2`), edge capacities, `k` unicast sessions `src i → dst i`, and a flag saying in which
directions each edge may be used (`d = true` is `(ends e).1 → (ends e).2`). An undirected network
has `usable = fun _ _ => true` and its capacity is shared by both directions; a directed network
has `usable = fun _ d => d`. -/
structure Network (nV nE k : ℕ) where
  ends : Fin nE → Fin nV × Fin nV
  cap : Fin nE → ℝ
  src : Fin k → Fin nV
  dst : Fin k → Fin nV
  usable : Fin nE → Bool → Bool

variable {nV nE k : ℕ}

/-- Tail of edge `e` traversed in direction `d`. -/
def Network.tail (N : Network nV nE k) (e : Fin nE) (d : Bool) : Fin nV :=
  if d then (N.ends e).1 else (N.ends e).2

/-- Head of edge `e` traversed in direction `d`. -/
def Network.head (N : Network nV nE k) (e : Fin nE) (d : Bool) : Fin nV :=
  if d then (N.ends e).2 else (N.ends e).1

/-- A transmission history: `h t e d` is the symbol sent in round `t` on edge `e`, direction `d`. -/
abbrev Hist (nE : ℕ) := ℕ → Fin nE → Bool → ℕ

/-- A zero-error causal network code (data). Block length `n` (normalizes rates and edge
budgets), `rounds` causal communication rounds, message-set sizes `M i`, alphabet sizes
`L t e d` per round/edge/direction, encoders and decoders. -/
structure NCode (N : Network nV nE k) where
  n : ℕ
  rounds : ℕ
  M : Fin k → ℕ
  L : ℕ → Fin nE → Bool → ℕ
  enc : ℕ → Fin nE → Bool → (Fin k → ℕ) → Hist nE → ℕ
  dec : Fin k → (Fin k → ℕ) → Hist nE → ℕ

/-- The messages known at node `v` (those of sessions whose source is `v`; others read `0`). -/
def Network.localMsgs (N : Network nV nE k) (w : Fin k → ℕ) (v : Fin nV) : Fin k → ℕ :=
  fun i => if N.src i = v then w i else 0

/-- What node `v` has received: the history restricted to edge-directions entering `v`. -/
def Network.view (N : Network nV nE k) (v : Fin nV) (h : Hist nE) : Hist nE :=
  fun s e d => if N.head e d = v then h s e d else 0

/-- Symbol sent in round `t` on `(e, d)`: the tail's encoder applied to its own messages and its
received history, reduced into the alphabet `Fin (L t e d)`. -/
def NCode.send {N : Network nV nE k} (C : NCode N) (w : Fin k → ℕ) (h : Hist nE) (t : ℕ)
    (e : Fin nE) (d : Bool) : ℕ :=
  C.enc t e d (N.localMsgs w (N.tail e d)) (N.view (N.tail e d) h) % C.L t e d

/-- History of the first `t` rounds (entries for rounds `≥ t` are `0`); round `t` only sees
rounds `< t`, which enforces causality. -/
def NCode.hist {N : Network nV nE k} (C : NCode N) (w : Fin k → ℕ) : ℕ → Hist nE
  | 0 => fun _ _ _ => 0
  | t + 1 => fun s e d => if s = t then C.send w (C.hist w t) t e d else C.hist w t s e d

/-- A valid zero-error code: positive sizes, unusable directions carry nothing, each edge's
total use over the block (both directions together) is at most `n · cap e` bits, and every
sink decodes its session's message correctly for every message tuple. -/
structure NCode.Valid {N : Network nV nE k} (C : NCode N) : Prop where
  n_pos : 1 ≤ C.n
  M_pos : ∀ i, 1 ≤ C.M i
  L_pos : ∀ t e d, 1 ≤ C.L t e d
  unusable : ∀ t e d, N.usable e d = false → C.L t e d = 1
  budget : ∀ e, ∑ t ∈ range C.rounds,
    (logb 2 (C.L t e true) + logb 2 (C.L t e false)) ≤ C.n * N.cap e
  zero_error : ∀ (w : (i : Fin k) → Fin (C.M i)) (i : Fin k),
    C.dec i (N.localMsgs (fun j => (w j : ℕ)) (N.dst i))
      (N.view (N.dst i) (C.hist (fun j => (w j : ℕ)) C.rounds)) = w i

/-- Zero-error network-coding capacity region (rates in bits per block-length unit). -/
def codingRegion (N : Network nV nE k) : Set (Fin k → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ ∀ ε > 0, ∃ C : NCode N, C.Valid ∧ ∀ i, r i - ε ≤ logb 2 (C.M i) / C.n}

/-- `p` is a walk from `u` to `v` using only usable edge-directions. -/
def Network.IsWalk (N : Network nV nE k) : Fin nV → Fin nV → List (Fin nE × Bool) → Prop
  | u, v, [] => u = v
  | u, v, x :: p => N.tail x.1 x.2 = u ∧ N.usable x.1 x.2 = true ∧ N.IsWalk (N.head x.1 x.2) v p

/-- A fractional multicommodity routing: each session is split over finitely many walks with
nonnegative weights; the total load on each (undirected) edge, summed over both directions and
all sessions, is at most its capacity. -/
structure Routing (N : Network nV nE k) where
  paths : Fin k → Finset (List (Fin nE × Bool))
  wt : Fin k → List (Fin nE × Bool) → ℝ
  wt_nonneg : ∀ i p, 0 ≤ wt i p
  walk : ∀ i, ∀ p ∈ paths i, N.IsWalk (N.src i) (N.dst i) p
  load_le : ∀ e, ∑ i, ∑ p ∈ paths i, wt i p * ((p.countP (fun x => x.1 = e) : ℕ) : ℝ) ≤ N.cap e

/-- Fractional routing rate region. -/
def routingRegion (N : Network nV nE k) : Set (Fin k → ℝ) :=
  {r | (∀ i, 0 ≤ r i) ∧ ∃ R : Routing N, ∀ i, r i ≤ ∑ p ∈ R.paths i, R.wt i p}

/-- **Open problem #342 (ProofAtlas, edition 2026-11-12): Li–Li undirected multiple-unicast
network coding conjecture.** Exact statement: "For every finite undirected edge-capacitated
network and every finite collection of independent source-destination unicast sessions, prove
or disprove that the zero-error network-coding capacity region equals the fractional
multicommodity-routing capacity region. Each undirected edge has a shared capacity bounding the
sum of transmission rates in its two directions; intermediate nodes may causally encode
received messages in the coding model. Fractional routing may split each session over paths.
The target uses the standard zero-error formulation, not multicast or directed networks."
Status: OPEN (the open question is whether this `Prop` or its negation holds). NOT proved.

Modelling and simplifications (all deliberate):
* Coding model (`NCode`): a block of length `n`; communication proceeds in finitely many
  causal rounds; in round `t` edge `e` carries in direction `d` one symbol of an alphabet of size
  `L t e d` chosen in advance (so no timing side channel); the symbol is computed by the tail
  node from its own sessions' messages and everything it received in earlier rounds; the total
  information on edge `e` over the block, both directions together, is at most `n · cap e`
  bits (`budget`). This per-block budget with free scheduling of the rounds is our formalization
  of "shared capacity" plus "causal encoding"; it contains the standard acyclic block-code model
  and is the usual time-expanded formulation, but other equivalent-in-the-limit formulations
  (per-time-slot capacities) exist. Zero error: correct decoding for every message tuple.
* Messages of distinct sessions are independent (all tuples must decode).
* Coding rate region: tuples `r ≥ 0` approached within every `ε` by valid codes.
* Routing: finitely many walks per session (walks may repeat edges; their load counts every
  traversal). The routing region is compared up to closure, a harmless normalization.
* Real (not necessarily rational) nonnegative capacities; multigraphs allowed. -/
def LiLiConjecture : Prop :=
  ∀ (nV nE k : ℕ) (N : Network nV nE k), (∀ e d, N.usable e d = true) → (∀ e, 0 ≤ N.cap e) →
    codingRegion N = closure (routingRegion N)

/-- Cut lemma: a walk from a node in `S` to a node outside `S` uses some usable
edge-direction leaving `S`. -/
theorem Network.IsWalk.exists_cross (N : Network nV nE k) (S : Finset (Fin nV)) :
    ∀ (p : List (Fin nE × Bool)) (u v : Fin nV), N.IsWalk u v p → u ∈ S → v ∉ S →
      ∃ x ∈ p, N.usable x.1 x.2 = true ∧ N.tail x.1 x.2 ∈ S ∧ N.head x.1 x.2 ∉ S := by
  intro p
  induction p with
  | nil => intro u v h hu hv; exact absurd (h ▸ hu) hv
  | cons x p ih =>
    intro u v h hu hv
    obtain ⟨ht, hus, hw⟩ := h
    by_cases hh : N.head x.1 x.2 ∈ S
    · obtain ⟨y, hy, hy'⟩ := ih _ v hw hh hv
      exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩
    · exact ⟨x, List.mem_cons_self, hus, ht ▸ hu, hh⟩

/-! ### The directed butterfly network (Ahlswede–Cai–Li–Yeung 2000), two-unicast form

Nodes: `0 = s₁`, `1 = s₂`, `2`, `3`, `4 = t₁`, `5 = t₂`. Directed unit-capacity edges
`e₀ : 0→2, e₁ : 1→2, e₂ : 2→3, e₃ : 3→4, e₄ : 3→5, e₅ : 0→5, e₆ : 1→4`.
Sessions `s₁ → t₁` and `s₂ → t₂`. THIS IS A DIRECTED NETWORK (`usable = fun _ d => d`); the
result below does not bear on the undirected Li–Li conjecture. -/

/-- The directed two-unicast butterfly network. -/
def butterfly : Network 6 7 2 where
  ends := ![(0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (0, 5), (1, 4)]
  cap := fun _ => 1
  src := ![0, 1]
  dst := ![4, 5]
  usable := fun _ d => d

/-- The round in which each edge is active in the XOR code. -/
def butterflyAct : Fin 7 → ℕ := ![0, 0, 1, 2, 2, 0, 0]

/-- The XOR network code: sources send their bits, node 2 sends `a ⊕ b`, node 3 forwards it;
`t₁` recovers `a = (a ⊕ b) ⊕ b`, `t₂` recovers `b = (a ⊕ b) ⊕ a`. -/
def butterflyCode : NCode butterfly where
  n := 1
  rounds := 3
  M := fun _ => 2
  L := fun t e d => if d = true ∧ t = butterflyAct e then 2 else 1
  enc := fun _ e _ loc h =>
    if e = 0 ∨ e = 5 then loc 0
    else if e = 1 ∨ e = 6 then loc 1
    else if e = 2 then h 0 0 true + h 0 1 true
    else h 1 2 true
  dec := fun i _ h =>
    if i = 0 then (h 2 3 true + h 0 6 true) % 2 else (h 2 4 true + h 0 5 true) % 2

theorem butterflyCode_correct : ∀ a < 2, ∀ b < 2, ∀ i : Fin 2,
    butterflyCode.dec i (butterfly.localMsgs ![a, b] (butterfly.dst i))
      (butterfly.view (butterfly.dst i) (butterflyCode.hist ![a, b] 3)) = ![a, b] i := by
  decide

theorem butterflyCode_valid : butterflyCode.Valid where
  n_pos := le_rfl
  M_pos := fun _ => show 1 ≤ 2 by norm_num
  L_pos := fun t e d => by simp only [butterflyCode]; split_ifs <;> norm_num
  unusable := fun t e d h => by
    simp only [butterfly] at h; subst h; simp [butterflyCode]
  budget := fun e => by
    fin_cases e <;>
      simp [butterflyCode, butterfly, butterflyAct, Finset.sum_range_succ]
  zero_error := fun w i => by
    have hw : (fun j => (w j : ℕ)) = ![(w 0 : ℕ), (w 1 : ℕ)] := by
      funext j; fin_cases j <;> rfl
    rw [hw]
    have h := butterflyCode_correct (w 0) (w 0).isLt (w 1) (w 1).isLt i
    refine h.trans ?_
    fin_cases i <;> rfl

/-- In the directed butterfly every walk of either session uses edge `e₂ : 2 → 3`. -/
theorem butterfly_walk_uses_middle (i : Fin 2) (p : List (Fin 7 × Bool))
    (hp : butterfly.IsWalk (butterfly.src i) (butterfly.dst i) p) :
    0 < p.countP (fun x => x.1 = 2) := by
  rw [List.countP_pos_iff]
  fin_cases i
  · obtain ⟨x, hx, h⟩ := Network.IsWalk.exists_cross butterfly {0, 2, 5} p _ _ hp
      (by decide) (by decide)
    refine ⟨x, hx, ?_⟩
    revert h; generalize x = x
    revert x; decide
  · obtain ⟨x, hx, h⟩ := Network.IsWalk.exists_cross butterfly {1, 2, 4} p _ _ hp
      (by decide) (by decide)
    refine ⟨x, hx, ?_⟩
    revert h; generalize x = x
    revert x; decide

/-- Routing bound in the directed butterfly: `r₀ + r₁ ≤ 1` (cut at edge `e₂`). -/
theorem butterfly_routing_le {r : Fin 2 → ℝ} (hr : r ∈ routingRegion butterfly) :
    r 0 + r 1 ≤ 1 := by
  obtain ⟨-, R, hR⟩ := hr
  have hload := R.load_le 2
  have hge : ∑ i, ∑ p ∈ R.paths i, R.wt i p ≤
      ∑ i, ∑ p ∈ R.paths i, R.wt i p * ((p.countP (fun x => x.1 = 2) : ℕ) : ℝ) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun p hp => ?_
    have h1 : (1 : ℝ) ≤ ((p.countP (fun x => x.1 = 2) : ℕ) : ℝ) := by
      exact_mod_cast butterfly_walk_uses_middle i p (R.walk i p hp)
    nlinarith [R.wt_nonneg i p]
  have : ∑ i, ∑ p ∈ R.paths i, R.wt i p = (∑ p ∈ R.paths 0, R.wt 0 p) +
      ∑ p ∈ R.paths 1, R.wt 1 p := Fin.sum_univ_two _
  have hcap : butterfly.cap 2 = 1 := rfl
  linarith [hR 0, hR 1]

/-- **Known result (Ahlswede–Cai–Li–Yeung, "Network information flow", IEEE Trans. Inf.
Theory 46 (2000)): network coding gain in the DIRECTED butterfly network.** With unit
capacities, the XOR code achieves the rate pair `(1, 1)` with zero error, while every
fractional routing has `r₀ + r₁ ≤ 1`; hence `(1, 1)` is not in the closure of the routing
region. This concerns a directed network only and says nothing about the undirected Li–Li
conjecture `LiLiConjecture`. -/
theorem butterfly_coding_gain :
    (fun _ => (1 : ℝ)) ∈ codingRegion butterfly ∧
      (fun _ => (1 : ℝ)) ∉ closure (routingRegion butterfly) := by
  refine ⟨⟨fun _ => zero_le_one, fun ε hε => ⟨butterflyCode, butterflyCode_valid, fun i => ?_⟩⟩, ?_⟩
  · simp only [butterflyCode, Nat.cast_one, div_one, Nat.cast_ofNat]
    rw [Real.logb_self_eq_one (by norm_num)]; linarith
  · intro hmem
    have hsub : closure (routingRegion butterfly) ⊆ {r : Fin 2 → ℝ | r 0 + r 1 ≤ 1} :=
      closure_minimal (fun r hr => butterfly_routing_le hr)
        (isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const)
    have := hsub hmem
    simp at this
    norm_num at this

end Network

end CryptoLean.OpenProblems.MultiUser

#print axioms CryptoLean.OpenProblems.MultiUser.sum_causalLaw
#print axioms CryptoLean.OpenProblems.MultiUser.sum_success_le
#print axioms CryptoLean.OpenProblems.MultiUser.relayCapacity_nonneg
#print axioms CryptoLean.OpenProblems.MultiUser.relayAchievable_zero
#print axioms CryptoLean.OpenProblems.MultiUser.relayAchievable_le_logb_card
#print axioms CryptoLean.OpenProblems.MultiUser.relayCapacity_le_logb_card
#print axioms CryptoLean.OpenProblems.MultiUser.bcAchievable_zero
#print axioms CryptoLean.OpenProblems.MultiUser.zero_mem_bcCapacityRegion
#print axioms CryptoLean.OpenProblems.MultiUser.bcAchievable_le
#print axioms CryptoLean.OpenProblems.MultiUser.butterflyCode_correct
#print axioms CryptoLean.OpenProblems.MultiUser.butterflyCode_valid
#print axioms CryptoLean.OpenProblems.MultiUser.butterfly_routing_le
#print axioms CryptoLean.OpenProblems.MultiUser.butterfly_coding_gain
