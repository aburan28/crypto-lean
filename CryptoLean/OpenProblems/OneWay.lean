import Mathlib

/-!
# One-way functions, one-way permutations and P vs BPP

Open problems (ProofAtlas cryptography list):
* #1  Existence of One-Way Functions        -> `OneWayFunctionsExist`  (OPEN, `def ... : Prop`)
* #4  One-Way Permutations                  -> `OneWayPermutationsExist` (OPEN, `def ... : Prop`)
* #2  P vs BPP                              -> `PEqualsBPP` (OPEN, `def ... : Prop`)
* #3  Basing OWF on NP-hardness             -> left informal, see the comment at the end.

None of these problems is solved here. What is proved are standard, known partial results:
* negligible functions (defined through Mathlib's `Asymptotics.SuperpolynomialDecay`) agree with
  the textbook "`|μ n| ≤ n^{-c}` eventually, for every `c`" definition, and are closed under
  sums and multiplication by polynomials;
* every one-way permutation is a one-way function, so `OneWayPermutationsExist` implies
  `OneWayFunctionsExist` (for any choice of efficiency class and adversary class);
* one-wayness is impossible against a computationally unbounded adversary: the brute-force
  inverter succeeds with probability `1`;
* `P ⊆ BPP` (the easy half of P vs BPP) for the concrete Turing-machine model below.

## Model

Mathlib has no probabilistic polynomial-time machines, so randomness is modelled explicitly:
an adversary at security parameter `n` is a deterministic function of its input and of
`coins n` uniformly random bits, and its success probability is an exact finite average over
inputs `x ∈ {0,1}^n` and coins `ω ∈ {0,1}^{coins n}`. Polynomial time is Mathlib's
`Turing.TM2ComputableInPolyTime` (multi-stack Turing machines with a polynomial step bound),
applied to bit strings `List Bool`.

Modelling simplifications (stated honestly):
* function families are length preserving, `f n : {0,1}^n → {0,1}^n`. For one-way functions this
  is without loss of generality (known result: Goldreich, *Foundations of Cryptography* I,
  Prop. 2.2.3 / §2.2.3), and one-way permutations are length preserving by definition;
* adversaries are uniform PPT machines (Goldreich FoC I, Def. 2.2.1); the non-uniform variant
  is a different, equally open, statement.
-/

namespace CryptoLean.OpenProblems.OneWay

open Filter Asymptotics Topology

/-! ## Negligible functions -/

/-- `μ` is negligible: it decays faster than every inverse polynomial. Defined as Mathlib's
`SuperpolynomialDecay` along `atTop` with parameter `n ↦ (n : ℝ)`. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  SuperpolynomialDecay atTop (fun n : ℕ => (n : ℝ)) μ

/-- Known result (textbook definition, Goldreich FoC I, Def. 1.3.5 / Katz–Lindell Def. 3.4):
`μ` is negligible iff for every `c` eventually `|μ n| ≤ 1 / n^c`. -/
theorem negligible_iff (μ : ℕ → ℝ) :
    Negligible μ ↔ ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, |μ n| ≤ 1 / (n : ℝ) ^ c := by
  constructor
  · intro h c
    have h1 : ∀ᶠ n : ℕ in atTop, |(n : ℝ) ^ c * μ n| < 1 := by
      have := (h c).abs
      simp only [abs_zero] at this
      exact this.eventually_lt_const one_pos
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    have hpos : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    rw [abs_mul, abs_of_pos hpos] at hn
    rw [le_div_iff₀ hpos]
    linarith [mul_comm ((n : ℝ) ^ c) |μ n|]
  · intro h z
    apply squeeze_zero_norm' _ tendsto_one_div_atTop_nhds_zero_nat
    filter_upwards [h (z + 1), eventually_ge_atTop 1] with n hn hn1
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hpos : (0 : ℝ) < (n : ℝ) ^ z := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    calc (n : ℝ) ^ z * |μ n| ≤ (n : ℝ) ^ z * (1 / (n : ℝ) ^ (z + 1)) :=
          mul_le_mul_of_nonneg_left hn hpos.le
      _ = 1 / (n : ℝ) := by
          rw [pow_succ]; field_simp

/-- Known result: the sum of two negligible functions is negligible. -/
theorem Negligible.add {μ ν : ℕ → ℝ} (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (μ + ν) :=
  SuperpolynomialDecay.add hμ hν

/-- Known result: a polynomial times a negligible function is negligible. -/
theorem Negligible.polynomial_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : Polynomial ℝ) :
    Negligible (fun n => p.eval (n : ℝ) * μ n) :=
  SuperpolynomialDecay.polynomial_mul hμ p

/-- Known result: a function eventually bounded in absolute value by a negligible one is
negligible. -/
theorem Negligible.of_abs_le {μ ν : ℕ → ℝ} (hμ : Negligible μ)
    (h : ∀ᶠ n in atTop, |ν n| ≤ |μ n|) : Negligible ν := by
  rw [negligible_iff] at hμ ⊢
  intro c
  filter_upwards [hμ c, h] with n h1 h2 using h2.trans h1

/-- Known (trivial) fact: the constant function `1` is not negligible. -/
theorem not_negligible_one : ¬ Negligible (fun _ => (1 : ℝ)) := by
  rw [negligible_iff]
  intro h
  obtain ⟨N, hN⟩ := (h 1).exists_forall_of_atTop
  have := hN (N + 2) (by omega)
  simp only [abs_one, pow_one] at this
  rw [le_div_iff₀ (by positivity)] at this
  push_cast at this
  linarith

/-! ## Function families, adversaries, one-wayness -/

/-- Bit strings of length `n`. -/
abbrev Word (n : ℕ) := Fin n → Bool

/-- A length-preserving function family `f n : {0,1}^n → {0,1}^n`. -/
abbrev Fam := ∀ n : ℕ, Word n → Word n

/-- A randomized inverter: on security parameter `n` it reads `y ∈ {0,1}^n` and
`coins n` random bits and outputs a candidate preimage in `{0,1}^n`. -/
structure Adversary where
  /-- number of random coins used at security parameter `n` -/
  coins : ℕ → ℕ
  /-- the deterministic algorithm, as a function of its input and coins -/
  run : ∀ n : ℕ, Word n → Word (coins n) → Word n

/-- Probability that `A` inverts `f` at length `n`:
`Pr_{x ← {0,1}^n, ω ← {0,1}^{coins n}} [ f(A(f x; ω)) = f x ]`, as an exact average. -/
noncomputable def successProb (f : Fam) (A : Adversary) (n : ℕ) : ℝ :=
  (∑ x : Word n, ∑ ω : Word (A.coins n),
      if f n (A.run n (f n x) ω) = f n x then (1 : ℝ) else 0) /
    ((2 : ℝ) ^ n * (2 : ℝ) ^ A.coins n)

/-- `f` is one-way relative to an efficiency class `Eff` and an adversary class `Adv`:
`f ∈ Eff` and every adversary in `Adv` inverts `f` with only negligible probability. -/
def IsOneWayFunction (Eff : Fam → Prop) (Adv : Adversary → Prop) (f : Fam) : Prop :=
  Eff f ∧ ∀ A, Adv A → Negligible (successProb f A)

/-- A one-way permutation: a one-way function each of whose members is a bijection. -/
def IsOneWayPermutation (Eff : Fam → Prop) (Adv : Adversary → Prop) (f : Fam) : Prop :=
  IsOneWayFunction Eff Adv f ∧ ∀ n, Function.Bijective (f n)

/-- Existence of a one-way function relative to `Eff` and `Adv`. -/
def OWFExists (Eff : Fam → Prop) (Adv : Adversary → Prop) : Prop :=
  ∃ f, IsOneWayFunction Eff Adv f

/-- Existence of a one-way permutation relative to `Eff` and `Adv`. -/
def OWPExists (Eff : Fam → Prop) (Adv : Adversary → Prop) : Prop :=
  ∃ f, IsOneWayPermutation Eff Adv f

/-- Known result (by definition; Goldreich FoC I, §2.4.1): every one-way permutation is a
one-way function. -/
theorem IsOneWayPermutation.isOneWayFunction {Eff : Fam → Prop} {Adv : Adversary → Prop}
    {f : Fam} (h : IsOneWayPermutation Eff Adv f) : IsOneWayFunction Eff Adv f :=
  h.1

/-- Known result: existence of one-way permutations implies existence of one-way functions
(ProofAtlas #4 ⇒ #1), for every efficiency class and adversary class. -/
theorem owfExists_of_owpExists {Eff : Fam → Prop} {Adv : Adversary → Prop}
    (h : OWPExists Eff Adv) : OWFExists Eff Adv :=
  let ⟨f, hf⟩ := h
  ⟨f, hf.isOneWayFunction⟩

/-! ## Unbounded adversaries invert everything -/

/-- The brute-force inverter for `f`: on input `y` it outputs some preimage of `y` if one exists
(no coins). It is not efficient in general. -/
noncomputable def bruteForce (f : Fam) : Adversary where
  coins := fun _ => 0
  run := fun n y _ => by
    classical
    exact if h : ∃ x, f n x = y then h.choose else y

/-- Known result: the brute-force inverter succeeds with probability exactly `1`. -/
theorem successProb_bruteForce (f : Fam) (n : ℕ) : successProb f (bruteForce f) n = 1 := by
  classical
  have key : ∀ (x : Word n) (ω : Word ((bruteForce f).coins n)),
      f n ((bruteForce f).run n (f n x) ω) = f n x := by
    intro x ω
    have hx : ∃ x', f n x' = f n x := ⟨x, rfl⟩
    simp only [bruteForce, hx, ↓reduceDIte]
    exact hx.choose_spec
  unfold successProb
  simp only [key, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [div_eq_one_iff_eq (by positivity)]
  simp

/-- Known result (Goldreich FoC I, §2.2): no function family is one-way against an adversary
class that contains its brute-force inverter. In particular one-wayness is only meaningful for
computationally bounded adversaries. -/
theorem not_isOneWayFunction_of_bruteForce_mem {Eff : Fam → Prop} {Adv : Adversary → Prop}
    {f : Fam} (hA : Adv (bruteForce f)) : ¬ IsOneWayFunction Eff Adv f := by
  rintro ⟨-, h⟩
  have := h _ hA
  have heq : successProb f (bruteForce f) = fun _ => (1 : ℝ) :=
    funext (successProb_bruteForce f)
  rw [heq] at this
  exact not_negligible_one this

/-- Known result: there are no one-way functions against all (unbounded) adversaries. -/
theorem not_owfExists_unbounded (Eff : Fam → Prop) : ¬ OWFExists Eff (fun _ => True) := by
  rintro ⟨f, hf⟩
  exact not_isOneWayFunction_of_bruteForce_mem trivial hf

/-! ## The concrete classes: polynomial-time Turing machines -/

/-- `g : {0,1}* → {0,1}*` is computable in polynomial time (Mathlib `TM2` machines, identity
encoding of bit strings). -/
def PolyTimeComputable (g : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) id g)

/-- `M : {0,1}* → {0,1}` is a polynomial-time decider. -/
def PolyTimeDecider (M : List Bool → Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) Computability.encodeBool M)

/-- The family `f` is uniformly computable in polynomial time. -/
def PolyTimeFam (f : Fam) : Prop :=
  ∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n (x : Word n), g (List.ofFn x) = List.ofFn (f n x)

/-- `A` is a (uniform) probabilistic polynomial-time adversary: it uses `p(n)` coins for a
polynomial `p`, and a single polynomial-time machine maps `y ++ ω` to its output. (Since
`|y| = n` and `n ↦ n + p(n)` is strictly increasing, the machine can split its input.) -/
def PPT (A : Adversary) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, A.coins n = p.eval n) ∧
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧
      ∀ n (y : Word n) (ω : Word (A.coins n)),
        g (List.ofFn y ++ List.ofFn ω) = List.ofFn (A.run n y ω)

/-- **Existence of one-way functions** (OPEN; ProofAtlas #1, "Existence of One-Way
Functions"): *there exists a function family computable in polynomial time such that every
probabilistic polynomial-time algorithm inverts it, on the image of a uniformly random input,
with only negligible probability.*

Modelling note: length-preserving families (w.l.o.g., Goldreich FoC I §2.2.3), uniform PPT
adversaries modelled by `PPT` over Mathlib `TM2` machines, exact success probability
`successProb`. Stated as a `Prop` only; it is NOT proved here (it would imply `P ≠ NP`). -/
def OneWayFunctionsExist : Prop := OWFExists PolyTimeFam PPT

/-- **Existence of one-way permutations** (OPEN; ProofAtlas #4, "One-Way Permutations"):
*there exists a polynomial-time computable family of permutations `f_n` of `{0,1}^n` that
is one-way against probabilistic polynomial-time inverters.*

Same model as `OneWayFunctionsExist`. Stated as a `Prop` only; it is NOT proved here.
(Open even assuming one-way functions exist: no black-box construction of OWPs from OWFs is
known, cf. Rudich 1988 / Kahn–Saks–Smyth 2000.) -/
def OneWayPermutationsExist : Prop := OWPExists PolyTimeFam PPT

/-- Known result: `OneWayPermutationsExist → OneWayFunctionsExist`. -/
theorem oneWayFunctionsExist_of_oneWayPermutationsExist
    (h : OneWayPermutationsExist) : OneWayFunctionsExist :=
  owfExists_of_owpExists h

/-! ## P vs BPP -/

/-- `L ∈ P`: decided by a deterministic polynomial-time machine. -/
def InP (L : Set (List Bool)) : Prop :=
  ∃ M : List Bool → Bool, PolyTimeDecider M ∧ ∀ x, (M x = true ↔ x ∈ L)

open Classical in
/-- `L ∈ BPP`: there are a polynomial `p` and a deterministic polynomial-time machine `M`
such that for every `x`, at least `2/3` of the coin strings `ω ∈ {0,1}^{p(|x|)}` make
`M(x ++ ω)` answer correctly. (`|x|` is recoverable from `|x ++ ω| = |x| + p(|x|)`.) -/
def InBPP (L : Set (List Bool)) : Prop :=
  ∃ p : Polynomial ℕ, ∃ M : List Bool → Bool, PolyTimeDecider M ∧ ∀ x : List Bool,
    2 * 2 ^ p.eval x.length ≤
      3 * (Finset.univ.filter (fun ω : Word (p.eval x.length) =>
        (M (x ++ List.ofFn ω) = true ↔ x ∈ L))).card

/-- **P vs BPP** (OPEN; ProofAtlas #2, "P vs BPP"): *is every language decidable by a
bounded-error probabilistic polynomial-time algorithm also decidable in deterministic
polynomial time, i.e. `P = BPP`?*

Modelling note: languages over `{0,1}`, Mathlib `TM2` machines, BPP with explicit coin strings
and error `≤ 1/3`. Stated as a `Prop` only; it is NOT proved here (it is conjectured true, and
follows from circuit lower bounds by Impagliazzo–Wigderson 1997). -/
def PEqualsBPP : Prop := ∀ L : Set (List Bool), InP L ↔ InBPP L

/-- Known result (`P ⊆ BPP`; Arora–Barak, *Computational Complexity*, §7.1): a deterministic
polynomial-time decider is a BPP machine that uses no coins. -/
theorem inBPP_of_inP {L : Set (List Bool)} (h : InP L) : InBPP L := by
  classical
  obtain ⟨M, hM, hL⟩ := h
  refine ⟨0, M, hM, fun x => ?_⟩
  have : (Finset.univ.filter (fun ω : Word ((0 : Polynomial ℕ).eval x.length) =>
      (M (x ++ List.ofFn ω) = true ↔ x ∈ L))) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro ω _
    simpa using hL x
  rw [this]
  simp

/-- Known result: P vs BPP reduces to the inclusion `BPP ⊆ P` (since `P ⊆ BPP`). -/
theorem pEqualsBPP_iff : PEqualsBPP ↔ ∀ L : Set (List Bool), InBPP L → InP L :=
  ⟨fun h L => (h L).2, fun h L => ⟨inBPP_of_inP, h L⟩⟩

/-! ## ProofAtlas #3: basing one-way functions on NP-hardness (left informal)

The question (OPEN; ProofAtlas #3, "Basing OWF on NP-hardness") asks whether the existence of
one-way functions can be derived from the worst-case hardness of `NP` (e.g. from
`NP ⊄ BPP`), typically via a (randomized, possibly adaptive) reduction that inverts any
candidate OWF with an oracle and thereby decides `SAT`. A faithful statement must quantify over
oracle reductions (oracle PPT machines and the class of allowed reductions: non-adaptive,
black-box, ...), which neither Mathlib nor this file models; known partial results are
*negative* barriers for restricted reductions (Feigenbaum–Fortnow 1993, Bogdanov–Trevisan 2006,
Akavia–Goldreich–Goldwasser–Moshkovitz 2006: such reductions would collapse the polynomial
hierarchy / give `NP ⊆ coAM`). A Prop with the oracle quantification replaced by something
weaker would misstate the problem, so it is deliberately not formalized here. -/

end CryptoLean.OpenProblems.OneWay

open CryptoLean.OpenProblems.OneWay in
#print axioms negligible_iff
open CryptoLean.OpenProblems.OneWay in
#print axioms Negligible.add
open CryptoLean.OpenProblems.OneWay in
#print axioms Negligible.polynomial_mul
open CryptoLean.OpenProblems.OneWay in
#print axioms Negligible.of_abs_le
open CryptoLean.OpenProblems.OneWay in
#print axioms not_negligible_one
open CryptoLean.OpenProblems.OneWay in
#print axioms IsOneWayPermutation.isOneWayFunction
open CryptoLean.OpenProblems.OneWay in
#print axioms owfExists_of_owpExists
open CryptoLean.OpenProblems.OneWay in
#print axioms successProb_bruteForce
open CryptoLean.OpenProblems.OneWay in
#print axioms not_isOneWayFunction_of_bruteForce_mem
open CryptoLean.OpenProblems.OneWay in
#print axioms not_owfExists_unbounded
open CryptoLean.OpenProblems.OneWay in
#print axioms oneWayFunctionsExist_of_oneWayPermutationsExist
open CryptoLean.OpenProblems.OneWay in
#print axioms inBPP_of_inP
open CryptoLean.OpenProblems.OneWay in
#print axioms pEqualsBPP_iff
