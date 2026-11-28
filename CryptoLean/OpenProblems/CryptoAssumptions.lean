import Mathlib
import CryptoLean.OpenProblems.OneWay

/-!
# Cryptographic assumptions: iO, LWE and LPN worst-case reductions

Open problems (ProofAtlas cryptography list, edition 2026-11-12):
* #126 Indistinguishability Obfuscation from Constant-Degree Homomorphic Assumptions
  -> `IOFromPolyStandardAssumptions` (OPEN, `def ... : Prop`)
* #232 Classical Worst-Case Hardness Reduction for LWE
  -> `ClassicalLWEReductionExists` (OPEN, `def ... : Prop`)
* #286 Worst-case to average-case hardness reduction for LPN
  -> `LPNWorstToAverageReductionExists` (OPEN, `def ... : Prop`)

None of these problems is solved here. Each one appears only as an unproved `def … : Prop`.
What is proved are standard, known facts:
* noiseless LWE/LPN is easy: if the rows `a_i` of the sample matrix span `(ZMod q)ⁿ` (`q` prime),
  the secret is uniquely determined by `b = A s` and recovered by a left inverse of `A`
  (`noiseless_exists_left_inverse`, `noiseless_recover`, `noiseless_secret_unique`);
* with zero noise the LWE distribution is distinguishable from uniform with advantage
  `≥ 1 - qⁿ/qᵐ` (`lwe_zero_noise_distinguishable`, `..._half`);
* truth tables as a canonical form for small-input circuits: the truth table of `C` preserves
  its functionality, equivalent circuits have identical truth tables (so no distinguisher can
  tell them apart), and for `k ≤ c · log₂(size)` inputs the table has `2^k ≤ size^c` entries
  (`truthTable_*`). The truth table is a list of bits, not a `Circ`, so this is *not* a proof
  that some `Obfuscator` satisfies `IsIO` (that would also need the polynomial-time
  computability of circuit evaluation on Turing machines, which is not formalized);
* the repetition code of length `n(2w+1)` has minimum distance `> 2w`, so the parameter
  constraints of the #286 statement are jointly satisfiable (`repMat_dist`,
  `lpn_params_satisfiable`).

## Model

Everything is stated in the PPT model of `CryptoLean.OpenProblems.OneWay`: polynomial time is
Mathlib's `Turing.TM2ComputableInPolyTime` on bit strings (`OneWay.PolyTimeComputable`),
randomness is an explicit uniformly random coin string `ω ∈ {0,1}^{coins n}`, and negligible is
`OneWay.Negligible`. To run machines on structured objects (matrices over `ZMod q`, circuits,
lattice bases, group-element encodings) we fix one explicit, self-delimiting binary encoding
`BinEnc` (binary numerals with doubled bits, length-prefixed lists). Any other reasonable
encoding is polynomially equivalent; this is not proved here.

**Black-box reductions.** A worst-case-to-average-case reduction is modelled as an
`OracleAlg`: a probabilistic machine that makes at most polynomially many *adaptive* queries to
an oracle, whose next-step function (next query or final output, as a function of input, coins and
the answers so far) is polynomial-time computable. The reduction must work for **every** oracle
(any Lean function, efficient or not) that solves the average-case problem; quantifying over all
oracles is what makes the statements non-vacuous (an inefficient brute-force solver is a legal
oracle, so a reduction cannot rely on the average-case problem being hard). Oracles are
deterministic functions; for the existence of a good oracle this is without loss of generality
(fixing the best coins of a randomized solver does not decrease its success probability), but
it is a modelling simplification (the reduction controls the oracle's coins).

**Constructions from assumptions** (#126) are modelled as implications between polynomial
hardness statements ("if these assumptions hold against all PPT adversaries with negligible
advantage, then this explicit construction is a secure iO"). Polynomial hardness of the
assumptions is exactly the "no sub-exponential loss" requirement. This is the usual meaning of
"construct X based on Y"; it is not a black-box (oracle) formulation. Pairing groups are given
by fixed public parameters `pp n` (`BilinearGen`) that every party receives (`IsPPTAdv`), rather
than by a randomized group generator; this avoids needing a deterministic polynomial-time
construction of large primes, which is an unrelated open problem.

**Probabilities** over finite sample spaces are exact finite averages; non-uniform noise is a
real weight function `χ : ZMod q → ℝ` (e.g. Regev's discretized Gaussian `dGauss`, defined from
Mathlib's `gaussianReal`). Weights are not required to sum to one in the definitions; the
intended instances do.

Things that are **not** formalized (stated honestly):
* quantum algorithms: Regev's quantum reduction is only described in prose (no quantum model in
  Mathlib); #232 asks for a *classical* reduction, which we can state;
* the *negative* answers to #232 / #286 ("no such reduction exists") would be black-box
  separation results and are not expressible as the negation of our Props (the negation of an
  existence-of-reduction Prop is a much weaker statement only about our specific model);
* sub-exponential hardness (the assumption under which iO is known, Jain–Lin–Sahai 2021/2022)
  needs time bounds beyond polynomial time and is only discussed in comments.
-/

namespace CryptoLean.OpenProblems.CryptoAssumptions

open CryptoLean.OpenProblems.OneWay
open Matrix

attribute [local instance] Classical.propDecidable

/-! ## Binary encodings -/

/-- A fixed binary encoding of objects as bit strings, used to feed them to Turing machines. -/
class BinEnc (α : Type*) where
  /-- the encoding -/
  enc : α → List Bool

export BinEnc (enc)

/-- Natural numbers: binary digits (least significant first), each bit `b` written as
`[true, b]`, terminated by `false` (self-delimiting, linear length). -/
instance : BinEnc ℕ := ⟨fun n => (n.bits.flatMap fun b => [true, b]) ++ [false]⟩

instance : BinEnc Bool := ⟨fun b => [b]⟩

instance : BinEnc ℤ := ⟨fun z => [decide (0 ≤ z)] ++ enc z.natAbs⟩

instance {k : ℕ} : BinEnc (Fin k) := ⟨fun i => enc i.val⟩

instance {q : ℕ} : BinEnc (ZMod q) := ⟨fun x => enc x.val⟩

instance : BinEnc ℚ := ⟨fun r => enc r.num ++ enc r.den⟩

instance {α β : Type*} [BinEnc α] [BinEnc β] : BinEnc (α × β) := ⟨fun p => enc p.1 ++ enc p.2⟩

instance {α β : Type*} [BinEnc α] [BinEnc β] : BinEnc (α ⊕ β) :=
  ⟨fun s => match s with
    | .inl a => false :: enc a
    | .inr b => true :: enc b⟩

instance {α : Type*} [BinEnc α] : BinEnc (Option α) :=
  ⟨fun o => match o with
    | none => [false]
    | some a => true :: enc a⟩

/-- Lists: length prefix, then the entries. -/
instance {α : Type*} [BinEnc α] : BinEnc (List α) := ⟨fun l => enc l.length ++ l.flatMap enc⟩

instance {α : Type*} [BinEnc α] {k : ℕ} : BinEnc (Fin k → α) := ⟨fun f => enc (List.ofFn f)⟩

instance {α : Type*} [BinEnc α] {m k : ℕ} : BinEnc (Matrix (Fin m) (Fin k) α) :=
  ⟨fun M => enc (fun i => (M i : Fin k → α))⟩

/-- The security parameter in unary, `1ⁿ0`. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-! ## Probabilistic polynomial-time algorithms -/

/-- A randomized algorithm family: at parameter `n` it reads `x : X n` and `coins n` random
bits and outputs an element of `Y n`. -/
structure RandAlg (X Y : ℕ → Type) where
  /-- number of random coins at parameter `n` -/
  coins : ℕ → ℕ
  /-- the deterministic algorithm, as a function of its input and coins -/
  run : ∀ n, X n → Word (coins n) → Y n

/-- `A` is probabilistic polynomial time *given the public string* `adv n` (a fixed public
parameter of polynomial length visible to every party, e.g. the description of a pairing group):
polynomially many coins, and one polynomial-time machine maps `1ⁿ0 ‖ enc (adv n) ‖ enc x ‖ ω`
to `enc (A n x ω)`. -/
def RandAlg.IsPPTAdv {X Y : ℕ → Type} [∀ n, BinEnc (X n)] [∀ n, BinEnc (Y n)]
    (adv : ℕ → List Bool) (A : RandAlg X Y) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, A.coins n ≤ p.eval n) ∧
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧
      ∀ n (x : X n) (ω : Word (A.coins n)),
        g (unary n ++ enc (adv n) ++ enc x ++ List.ofFn ω) = enc (A.run n x ω)

/-- `A` is (uniform) probabilistic polynomial time: `IsPPTAdv` with the empty public string. -/
def RandAlg.IsPPT {X Y : ℕ → Type} [∀ n, BinEnc (X n)] [∀ n, BinEnc (Y n)]
    (A : RandAlg X Y) : Prop :=
  A.IsPPTAdv (fun _ => [])

/-- Uniform average of `f` over a finite type. -/
noncomputable def avg {S : Type*} [Fintype S] (f : S → ℝ) : ℝ :=
  (∑ s, f s) / Fintype.card S

/-- Probability, over uniform coins, that a randomized decider accepts. -/
noncomputable def acc {X : ℕ → Type} (D : RandAlg X (fun _ => Bool)) (n : ℕ) (x : X n) : ℝ :=
  avg fun ω : Word (D.coins n) => if D.run n x ω then (1 : ℝ) else 0

/-- Probability over `c` uniform coins of an event. -/
noncomputable def probCoins (c : ℕ) (P : Word c → Prop) : ℝ :=
  avg fun ω : Word c => if P ω then (1 : ℝ) else 0

/-! ## Oracle algorithms (black-box reductions) -/

/-- An adaptive probabilistic oracle algorithm. At parameter `n`, on input `x` and coins `ω`,
given the list of oracle answers received so far, `next` returns either the next query
(`Sum.inl`) or the final output (`Sum.inr`). At most `maxQueries n` queries are made. -/
structure OracleAlg (X Q A Y : ℕ → Type) where
  /-- number of random coins -/
  coins : ℕ → ℕ
  /-- query budget -/
  maxQueries : ℕ → ℕ
  /-- next-step function -/
  next : ∀ n, X n → Word (coins n) → List (A n) → Q n ⊕ Y n

/-- Run a next-step function against an oracle with a query budget; `none` if the budget is
exhausted without an output. -/
def runFuel {Q A Y : Type} (step : List A → Q ⊕ Y) (O : Q → A) : ℕ → List A → Option Y
  | 0, h => match step h with
    | .inr y => some y
    | .inl _ => none
  | k + 1, h => match step h with
    | .inr y => some y
    | .inl q => runFuel step O k (h ++ [O q])

/-- The output of `R` with oracle `O` (`none` = no output within the query budget). -/
def OracleAlg.run {X Q A Y : ℕ → Type} (R : OracleAlg X Q A Y) (n : ℕ) (x : X n)
    (ω : Word (R.coins n)) (O : Q n → A n) : Option (Y n) :=
  runFuel (R.next n x ω) O (R.maxQueries n) []

/-- `R` is a probabilistic polynomial-time oracle machine: polynomially many coins and queries,
and its next-step function is polynomial-time computable (so every query and the output have
polynomial length, and the total running time, counting each oracle call as one step, is
polynomial). -/
def OracleAlg.IsPPT {X Q A Y : ℕ → Type} [∀ n, BinEnc (X n)] [∀ n, BinEnc (Q n)]
    [∀ n, BinEnc (A n)] [∀ n, BinEnc (Y n)] (R : OracleAlg X Q A Y) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, R.coins n ≤ p.eval n) ∧ (∀ n, R.maxQueries n ≤ p.eval n) ∧
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧
      ∀ n (x : X n) (ω : Word (R.coins n)) (h : List (A n)), h.length ≤ R.maxQueries n →
        g (unary n ++ enc x ++ enc h ++ List.ofFn ω) = enc (R.next n x ω h)

/-! ## LWE and LPN -/

/-- `m` samples of dimension `n` modulo `q`: a matrix `A` (rows `aᵢ`) and the vector `b`. -/
abbrev LWEInst (q : ℕ+) (m n : ℕ) := Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q)

/-- Regev's discretized Gaussian `Ψ̄_α` on `ZMod q`: the weight of `k` is the probability that
`round(q·X) ≡ k (mod q)` for `X` normal with mean `0` and standard deviation `α/√(2π)`
(Regev 2005/2009, §2). -/
noncomputable def dGauss (q : ℕ) (α : ℝ) (k : ZMod q) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (α ^ 2 / (2 * Real.pi)))).real
    {x : ℝ | (((round ((q : ℝ) * x) : ℤ)) : ZMod q) = k}

/-- Bernoulli(`τ`) noise on `ZMod 2` (standard binary LPN). -/
def bernoulliNoise (τ : ℝ) (e : ZMod 2) : ℝ := if e = 0 then 1 - τ else τ

/-- LPN noise over `ZMod p`: with probability `τ` the error is uniform in `ZMod p`, otherwise
`0` (the large-field LPN of Jain–Lin–Sahai). -/
noncomputable def fieldLPNNoise (p : ℕ) (τ : ℝ) (e : ZMod p) : ℝ :=
  if e = 0 then 1 - τ + τ / p else τ / p

/-- The zero-noise weight (`e = 0` with probability one). -/
def zeroNoise (q : ℕ) (e : ZMod q) : ℝ := if e = 0 then 1 else 0

/-- Weight of a noise vector: independent coordinates. -/
def noiseWeight {q : ℕ} {m : ℕ} (χ : ZMod q → ℝ) (e : Fin m → ZMod q) : ℝ := ∏ i, χ (e i)

/-- Expectation of `f (A, A s + e)` for `A, s` uniform and `e ← χᵐ` (the LWE/LPN distribution
`A_{s,χ}` with `m` samples and a uniformly random secret). -/
noncomputable def lweExp (q : ℕ+) (m n : ℕ) (χ : ZMod q → ℝ) (f : LWEInst q m n → ℝ) : ℝ :=
  (∑ A : Matrix (Fin m) (Fin n) (ZMod q), ∑ s : Fin n → ZMod q, ∑ e : Fin m → ZMod q,
      noiseWeight χ e * f (A, A *ᵥ s + e)) /
    (Fintype.card (Matrix (Fin m) (Fin n) (ZMod q)) * Fintype.card (Fin n → ZMod q))

/-- Expectation of `f (A, b)` for `A, b` uniform. -/
noncomputable def unifExp (q : ℕ+) (m n : ℕ) (f : LWEInst q m n → ℝ) : ℝ := avg f

/-- Advantage of a deterministic test `O` in distinguishing LWE samples from uniform. -/
noncomputable def lweAdv (q : ℕ+) (m n : ℕ) (χ : ZMod q → ℝ) (O : LWEInst q m n → Bool) : ℝ :=
  |lweExp q m n χ (fun x => if O x then 1 else 0) - unifExp q m n (fun x => if O x then 1 else 0)|

/-- Search success probability of a deterministic solver `O` for a *fixed* secret `s`:
`Pr_{A, e ← χᵐ}[O(A, A s + e) = s]`. -/
noncomputable def searchSuccFixed (q : ℕ+) (m n : ℕ) (χ : ZMod q → ℝ)
    (O : LWEInst q m n → (Fin n → ZMod q)) (s : Fin n → ZMod q) : ℝ :=
  (∑ A : Matrix (Fin m) (Fin n) (ZMod q), ∑ e : Fin m → ZMod q,
      noiseWeight χ e * (if O (A, A *ᵥ s + e) = s then 1 else 0)) /
    Fintype.card (Matrix (Fin m) (Fin n) (ZMod q))

/-- Average-case search success: `Pr_{A, s, e}[O(A, A s + e) = s]`. -/
noncomputable def searchSuccAvg (q : ℕ+) (m n : ℕ) (χ : ZMod q → ℝ)
    (O : LWEInst q m n → (Fin n → ZMod q)) : ℝ :=
  avg fun s => searchSuccFixed q m n χ O s

/-- Decision advantage of a randomized distinguisher family (dimension `n` = security
parameter, modulus `q n`, `m n` samples, noise weights `χ n`). -/
noncomputable def decAdv (q : ℕ → ℕ+) (m : ℕ → ℕ) (χ : ∀ n, ZMod (q n) → ℝ)
    (D : RandAlg (fun n => LWEInst (q n) (m n) n) (fun _ => Bool)) (n : ℕ) : ℝ :=
  |lweExp (q n) (m n) n (χ n) (acc D n) - unifExp (q n) (m n) n (acc D n)|

/-- Polynomial hardness of decision LWE/LPN with these parameters against PPT distinguishers
that also see the public string `adv n`: every such distinguisher has negligible advantage. -/
def DecisionHardAdv (adv : ℕ → List Bool) (q : ℕ → ℕ+) (m : ℕ → ℕ)
    (χ : ∀ n, ZMod (q n) → ℝ) : Prop :=
  ∀ D : RandAlg (fun n => LWEInst (q n) (m n) n) (fun _ => Bool), D.IsPPTAdv adv →
    Negligible (decAdv q m χ D)

/-- Polynomial hardness of decision LWE/LPN against uniform PPT distinguishers. -/
def DecisionHard (q : ℕ → ℕ+) (m : ℕ → ℕ) (χ : ∀ n, ZMod (q n) → ℝ) : Prop :=
  DecisionHardAdv (fun _ => []) q m χ

/-- A function `ℕ → ℕ` is polynomially bounded. -/
def PolyBounded (f : ℕ → ℕ) : Prop := ∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n

/-! ### Known result: noiseless LWE/LPN is easy -/

/-- Known result (linear algebra; e.g. Regev 2009 §1, Pietrzak 2012 "Cryptography from LPN",
§1: without noise the secret is found by Gaussian elimination). If the rows of `A` span `Kⁿ`
then `A` has a left inverse. -/
theorem noiseless_exists_left_inverse {K : Type*} [Field K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (h : Submodule.span K (Set.range A) = ⊤) :
    ∃ L : Matrix (Fin n) (Fin m) K, L * A = 1 := by
  have hr : (Aᵀ).mulVecLin.range = ⊤ := by
    rw [Matrix.range_mulVecLin]
    convert h using 3; rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective _ hr
  refine ⟨(LinearMap.toMatrix' g)ᵀ, ?_⟩
  have : Aᵀ * LinearMap.toMatrix' g = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id,
      show LinearMap.toMatrix' (Aᵀ).mulVecLin = Aᵀ from LinearMap.toMatrix'_toLin' _] at this
    exact this
  have := congrArg Matrix.transpose this
  simpa [Matrix.transpose_mul] using this

/-- Known result (noiseless LWE / LPN is solved by linear algebra): over `ZMod q`, `q` prime, if
the sample vectors `aᵢ` span `(ZMod q)ⁿ`, then a single matrix `L` (computable by Gaussian
elimination from `A` alone) recovers every secret from noiseless samples `b = A s`. For `q = 2`
this is noiseless LPN. This is why the noise in LWE/LPN is essential. -/
theorem noiseless_recover {q m n : ℕ} [Fact q.Prime] (A : Matrix (Fin m) (Fin n) (ZMod q))
    (h : Submodule.span (ZMod q) (Set.range A) = ⊤) :
    ∃ L : Matrix (Fin n) (Fin m) (ZMod q), ∀ s : Fin n → ZMod q, L *ᵥ (A *ᵥ s) = s := by
  obtain ⟨L, hL⟩ := noiseless_exists_left_inverse A h
  exact ⟨L, fun s => by rw [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec]⟩

/-- Known result: under the same spanning hypothesis the secret is uniquely determined by
noiseless samples. -/
theorem noiseless_secret_unique {q m n : ℕ} [Fact q.Prime] (A : Matrix (Fin m) (Fin n) (ZMod q))
    (h : Submodule.span (ZMod q) (Set.range A) = ⊤) {s s' : Fin n → ZMod q}
    (hs : A *ᵥ s = A *ᵥ s') : s = s' := by
  obtain ⟨L, hL⟩ := noiseless_recover A h
  rw [← hL s, ← hL s', hs]

/-! ### Known result: zero-noise decision LWE is easy -/

lemma noiseWeight_zeroNoise {q m : ℕ} (e : Fin m → ZMod q) :
    noiseWeight (zeroNoise q) e = if e = 0 then 1 else 0 := by
  unfold noiseWeight zeroNoise
  by_cases he : e = 0
  · simp [he]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false he)]
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra hc; push Not at hc; exact he (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Known result (folklore; the reason LWE needs noise): with zero noise, the test
"`b` lies in the column space of `A`" (decidable by Gaussian elimination) accepts LWE samples
with probability `1` and uniform samples with probability at most `qⁿ/qᵐ`, so its advantage is
at least `1 - qⁿ/qᵐ`. (Efficiency of the test is standard but not formalized here.) -/
theorem lwe_zero_noise_distinguishable (q : ℕ+) (m n : ℕ) :
    ∃ O : LWEInst q m n → Bool,
      1 - (q : ℝ) ^ n / (q : ℝ) ^ m ≤ lweAdv q m n (zeroNoise q) O := by
  refine ⟨fun x => decide (∃ s, x.1 *ᵥ s = x.2), ?_⟩
  have hreal : lweExp q m n (zeroNoise q)
      (fun x => if decide (∃ s, x.1 *ᵥ s = x.2) then 1 else 0) = 1 := by
    unfold lweExp
    simp_rw [noiseWeight_zeroNoise, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, add_zero]
    have : ∀ (A : Matrix (Fin m) (Fin n) (ZMod q)) (s : Fin n → ZMod q),
        (if decide (∃ s', A *ᵥ s' = A *ᵥ s) = true then (1 : ℝ) else 0) = 1 := by
      intro A s; simp only [decide_eq_true_eq]; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨s, rfl⟩)
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [div_self]
    positivity
  have hunif : unifExp q m n (fun x => if decide (∃ s, x.1 *ᵥ s = x.2) then 1 else 0) ≤
      (q : ℝ) ^ n / (q : ℝ) ^ m := by
    unfold unifExp avg
    rw [Fintype.sum_prod_type]
    have hA : ∀ A : Matrix (Fin m) (Fin n) (ZMod q),
        (∑ b : Fin m → ZMod q, if decide (∃ s, (A, b).1 *ᵥ s = (A, b).2) then (1 : ℝ) else 0)
          ≤ (q : ℝ) ^ n := by
      intro A
      simp only [decide_eq_true_eq]
      rw [Finset.sum_boole]
      have : (Finset.univ.filter fun b : Fin m → ZMod q => ∃ s, A *ᵥ s = b) =
          Finset.univ.image (fun s => A *ᵥ s) := by
        ext b; simp
      rw [this]
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin n → ZMod q)))
        (f := fun s => A *ᵥ s)
      have hc : (Finset.univ : Finset (Fin n → ZMod q)).card = (q : ℕ) ^ n := by
        simp [ZMod.card]
      rw [hc] at this
      exact_mod_cast this
    have hcard : (Fintype.card (Matrix (Fin m) (Fin n) (ZMod q) × (Fin m → ZMod q)) : ℝ) =
        (Fintype.card (Matrix (Fin m) (Fin n) (ZMod q)) : ℝ) * (q : ℝ) ^ m := by
      rw [Fintype.card_prod]; push_cast; congr 1; simp [ZMod.card]
    rw [hcard, div_le_div_iff₀ (by positivity) (by positivity)]
    calc (∑ A : Matrix (Fin m) (Fin n) (ZMod q), ∑ b : Fin m → ZMod q,
            if decide (∃ s, (A, b).1 *ᵥ s = (A, b).2) then (1 : ℝ) else 0) * (q : ℝ) ^ m
        ≤ (∑ _A : Matrix (Fin m) (Fin n) (ZMod q), (q : ℝ) ^ n) * (q : ℝ) ^ m := by
          gcongr with A; exact hA A
      _ = (q : ℝ) ^ n *
            ((Fintype.card (Matrix (Fin m) (Fin n) (ZMod q)) : ℝ) * (q : ℝ) ^ m) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  unfold lweAdv
  rw [hreal]
  calc 1 - (q : ℝ) ^ n / (q : ℝ) ^ m
      ≤ 1 - unifExp q m n (fun x => if decide (∃ s, x.1 *ᵥ s = x.2) then 1 else 0) := by
        linarith
    _ ≤ _ := le_abs_self _

/-- Known result (corollary): with zero noise, `q ≥ 2` and more samples than the dimension
(`m > n`), the column-space test has advantage at least `1/2`. -/
theorem lwe_zero_noise_distinguishable_half (q : ℕ+) (m n : ℕ) (hq : 2 ≤ (q : ℕ))
    (hmn : n < m) : ∃ O : LWEInst q m n → Bool, 1 / 2 ≤ lweAdv q m n (zeroNoise q) O := by
  obtain ⟨O, hO⟩ := lwe_zero_noise_distinguishable q m n
  refine ⟨O, le_trans ?_ hO⟩
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have : (q : ℝ) ^ n / (q : ℝ) ^ m ≤ 1 / 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
    rw [pow_add, pow_add, pow_one, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h1 (le_of_lt (mul_pos hpos (by linarith : (0:ℝ) < q)))]
  linarith

/-! ## Circuits and indistinguishability obfuscation -/

/-- A Boolean circuit as a straight-line program of NAND gates: wires `0, …, inputs-1` are the
inputs, gate `j` reads two earlier wires (out-of-range indices read `false`) and creates wire
`inputs + j`; the output is the last wire. -/
structure Circ where
  /-- number of input bits -/
  inputs : ℕ
  /-- gates, each given by the indices of its two input wires -/
  gates : List (ℕ × ℕ)

instance : BinEnc Circ := ⟨fun C => enc C.inputs ++ enc C.gates⟩

/-- Append one NAND gate's output wire. -/
def Circ.step (ws : List Bool) (g : ℕ × ℕ) : List Bool :=
  ws ++ [!(ws.getD g.1 false && ws.getD g.2 false)]

/-- Evaluate a circuit. -/
def Circ.eval (C : Circ) (x : Fin C.inputs → Bool) : Bool :=
  (C.gates.foldl Circ.step (List.ofFn x)).getLastD false

/-- Size: inputs plus gates. -/
def Circ.size (C : Circ) : ℕ := C.inputs + C.gates.length

/-- Functional equivalence: same input length and the same function. -/
def Circ.Equiv (C D : Circ) : Prop :=
  ∃ h : C.inputs = D.inputs, ∀ x, C.eval x = D.eval (fun i => x (Fin.cast h.symm i))

/-- A (randomized) obfuscator: on security parameter `n` and circuit `C` it uses
`coins n |C|` random bits and outputs a circuit. -/
structure Obfuscator where
  /-- coins as a function of the security parameter and the circuit size -/
  coins : ℕ → ℕ → ℕ
  /-- the algorithm -/
  run : ∀ (n : ℕ) (C : Circ), Word (coins n C.size) → Circ

/-- The obfuscator runs in probabilistic polynomial time (in `n + |C|`), given the public
string `adv n`. -/
def Obfuscator.IsPPTAdv (adv : ℕ → List Bool) (O : Obfuscator) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n s, O.coins n s ≤ p.eval (n + s)) ∧
    ∃ g : List Bool → List Bool, PolyTimeComputable g ∧
      ∀ n C (ω : Word (O.coins n C.size)),
        g (unary n ++ enc (adv n) ++ enc C ++ List.ofFn ω) = enc (O.run n C ω)

/-- The obfuscator runs in (uniform) probabilistic polynomial time. -/
def Obfuscator.IsPPT (O : Obfuscator) : Prop := O.IsPPTAdv (fun _ => [])

/-- Perfect functionality preservation: every obfuscation is equivalent to the circuit. -/
def Obfuscator.Correct (O : Obfuscator) : Prop :=
  ∀ n C (ω : Word (O.coins n C.size)), (O.run n C ω).Equiv C

/-- Probability that `D`, given both circuits and an obfuscation of `C`, outputs `1`. -/
noncomputable def ioAcc (O : Obfuscator) (D : RandAlg (fun _ => Circ × Circ × Circ) (fun _ => Bool))
    (n : ℕ) (C₀ C₁ C : Circ) : ℝ :=
  avg fun ω : Word (O.coins n C.size) => acc D n (C₀, C₁, O.run n C ω)

/-- Indistinguishability security against PPT distinguishers (that see the public string
`adv n`): for every polynomial size bound and all families of pairs of equivalent circuits of
equal size, every PPT distinguisher that is given both circuits has negligible advantage in
telling `O(C₀)` from `O(C₁)`. -/
def Obfuscator.IsIndistAdv (adv : ℕ → List Bool) (O : Obfuscator) : Prop :=
  ∀ (s : Polynomial ℕ) (C₀ C₁ : ℕ → Circ),
    (∀ n, (C₀ n).size ≤ s.eval n ∧ (C₀ n).size = (C₁ n).size ∧ (C₀ n).Equiv (C₁ n)) →
    ∀ D : RandAlg (fun _ => Circ × Circ × Circ) (fun _ => Bool), D.IsPPTAdv adv →
      Negligible fun n => |ioAcc O D n (C₀ n) (C₁ n) (C₀ n) - ioAcc O D n (C₀ n) (C₁ n) (C₁ n)|

/-- Indistinguishability security against uniform PPT distinguishers. -/
def Obfuscator.IsIndist (O : Obfuscator) : Prop := O.IsIndistAdv (fun _ => [])

/-- Indistinguishability obfuscation (Barak et al. 2001/2012; Garg–Gentry–Halevi–Raykova–Sahai–
Waters 2013): PPT, perfectly correct, and indistinguishable. -/
def Obfuscator.IsIO (O : Obfuscator) : Prop := O.IsPPT ∧ O.Correct ∧ O.IsIndist

/-! ### Known result: truth tables are a perfect iO for small-input circuits -/

/-- Index of an input `x ∈ {0,1}ᵏ` in `{0, …, 2ᵏ-1}`. -/
def boolIdx (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The truth-table "obfuscation": the input length and the list of all `2ᵏ` outputs. -/
def truthTable (C : Circ) : ℕ × List Bool :=
  (C.inputs, List.ofFn fun i : Fin (2 ^ C.inputs) => C.eval ((boolIdx C.inputs).symm i))

/-- Evaluating a truth table (a table lookup). -/
def evalTT (P : ℕ × List Bool) (x : Fin P.1 → Bool) : Bool := P.2.getD (boolIdx P.1 x) false

/-- Known result (folklore: a truth table is a canonical form, cf. Barak et al. 2012 §1 on
obfuscating small-domain functions): the truth table preserves functionality. -/
theorem truthTable_correct (C : Circ) (x : Fin C.inputs → Bool) :
    evalTT (truthTable C) x = C.eval x := by
  simp only [evalTT, truthTable]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [Fin.is_lt, Fin.eta, dite_true, Option.getD_some]
  exact congrArg C.eval ((boolIdx C.inputs).symm_apply_apply x)

/-- Known result: equivalent circuits have identical truth tables (canonical form). -/
theorem truthTable_eq_of_equiv {C D : Circ} (h : C.Equiv D) : truthTable C = truthTable D := by
  obtain ⟨k, g⟩ := C
  obtain ⟨k', g'⟩ := D
  obtain ⟨hk, hx⟩ := h
  dsimp only at hk
  subst hk
  simp only [truthTable, Prod.mk.injEq, true_and]
  congr 1
  funext i
  simpa using hx ((boolIdx k).symm i)

/-- Known result: the truth-table obfuscator is *perfectly* indistinguishable: for equivalent
circuits every (even unbounded) randomized distinguisher, given both circuits, has advantage
exactly `0`. -/
theorem truthTable_adv_zero {C₀ C₁ : Circ} (h : C₀.Equiv C₁) (c : ℕ)
    (D : Circ × Circ × (ℕ × List Bool) → Word c → Bool) :
    |probCoins c (fun ω => D (C₀, C₁, truthTable C₀) ω = true) -
      probCoins c (fun ω => D (C₀, C₁, truthTable C₁) ω = true)| = 0 := by
  rw [truthTable_eq_of_equiv h, sub_self, abs_zero]

/-- Known result: if `k ≤ c · log₂ |C|` then the truth table has `2ᵏ ≤ |C|ᶜ` entries, so the
truth-table obfuscator runs in polynomial time on this circuit class (evaluating `C` on all `2ᵏ`
inputs costs `2ᵏ · poly(|C|)`). -/
theorem truthTable_length_le (C : Circ) (c : ℕ) (hC : C.size ≠ 0)
    (hk : C.inputs ≤ c * Nat.log 2 C.size) : (truthTable C).2.length ≤ C.size ^ c := by
  simp only [truthTable, List.length_ofFn]
  calc 2 ^ C.inputs ≤ 2 ^ (c * Nat.log 2 C.size) := Nat.pow_le_pow_right (by norm_num) hk
    _ = (2 ^ Nat.log 2 C.size) ^ c := by rw [mul_comm, pow_mul]
    _ ≤ C.size ^ c := Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hC) c

/-! ## Bilinear groups and SXDH -/

/-- A family of prime-order asymmetric bilinear groups with **fixed public parameters**, in the
*representation* model: `pp n` is a public description string of the group at security
parameter `n` (e.g. the prime, curve coefficients and generators), and `rep₁ n a`, `rep₂ n a`,
`rep_T n a` are the bit-string encodings of `a·g₁ ∈ G₁`, `a·g₂ ∈ G₂`, `a·g_T ∈ G_T` for
`a ∈ ZMod (p n)`. The pairing `e(a g₁, b g₂) = ab g_T` is encoded in `IsEfficient`.

The public parameters are *given* (to every party), not computed from `1ⁿ`: a deterministic
polynomial-time construction of primes `≥ 2ⁿ` is itself an open problem (Polymath4), and
concrete pairing families (BN, BLS) find their primes by randomized search. Giving `pp n` as a
public string avoids entangling #126 with that unrelated problem. -/
structure BilinearGen where
  /-- public parameters (group description) -/
  pp : ℕ → List Bool
  /-- the prime group order -/
  p : ℕ → ℕ+
  /-- representation of `G₁` -/
  rep₁ : ∀ n, ZMod (p n) → List Bool
  /-- representation of `G₂` -/
  rep₂ : ∀ n, ZMod (p n) → List Bool
  /-- representation of `G_T` -/
  repT : ∀ n, ZMod (p n) → List Bool

/-- The family is a genuine, efficient bilinear group family: prime order `p n ≥ 2ⁿ` of
polynomial bit length, public parameters and injective representations of polynomial length,
and polynomial-time (given `pp n`) extraction of `p n`, `g₁`, `g₂`, group operations and
pairing on representations.

This is satisfiable without any open problem (Bertrand's postulate gives a prime in
`[2ⁿ, 2ⁿ⁺¹)`; put it in `pp n` and represent every group by `a ↦ enc a.val` with the pairing
being multiplication mod `p`; DDH is of course easy in that instance). That satisfiability is
not proved in Lean, because polynomial-time computability of modular arithmetic on Mathlib's
Turing machines is not formalized. -/
def BilinearGen.IsEfficient (G : BilinearGen) : Prop :=
  (∀ n, (G.p n : ℕ).Prime) ∧ (∀ n, 2 ^ n ≤ (G.p n : ℕ)) ∧
  (∀ n, Function.Injective (G.rep₁ n) ∧ Function.Injective (G.rep₂ n) ∧
    Function.Injective (G.repT n)) ∧
  (∃ P : Polynomial ℕ, ∀ n a, (G.p n : ℕ) < 2 ^ P.eval n ∧ (G.pp n).length ≤ P.eval n ∧
    (G.rep₁ n a).length ≤ P.eval n ∧
    (G.rep₂ n a).length ≤ P.eval n ∧ (G.repT n a).length ≤ P.eval n) ∧
  (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n, g (enc (G.pp n)) = enc ((G.p n : ℕ), G.rep₁ n 1, G.rep₂ n 1)) ∧
  (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n (a b : ZMod (G.p n)), g (enc (G.pp n) ++ enc (G.rep₁ n a, G.rep₁ n b)) =
      G.rep₁ n (a + b)) ∧
  (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n (a b : ZMod (G.p n)), g (enc (G.pp n) ++ enc (G.rep₂ n a, G.rep₂ n b)) =
      G.rep₂ n (a + b)) ∧
  (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n (a b : ZMod (G.p n)), g (enc (G.pp n) ++ enc (G.repT n a, G.repT n b)) =
      G.repT n (a + b)) ∧
  (∃ g : List Bool → List Bool, PolyTimeComputable g ∧
    ∀ n (a b : ZMod (G.p n)), g (enc (G.pp n) ++ enc (G.rep₁ n a, G.rep₂ n b)) =
      G.repT n (a * b))

/-- DDH advantage in the group with representation `rep`: distinguish `(a g, b g, ab g)` from
`(a g, b g, c g)` for uniform `a, b, c`. -/
noncomputable def ddhAdv (p : ℕ → ℕ+) (rep : ∀ n, ZMod (p n) → List Bool)
    (D : RandAlg (fun _ => List Bool × List Bool × List Bool) (fun _ => Bool)) (n : ℕ) : ℝ :=
  |avg (fun ab : ZMod (p n) × ZMod (p n) =>
      acc D n (rep n ab.1, rep n ab.2, rep n (ab.1 * ab.2))) -
    avg (fun abc : ZMod (p n) × ZMod (p n) × ZMod (p n) =>
      acc D n (rep n abc.1, rep n abc.2.1, rep n abc.2.2))|

/-- The SXDH assumption (polynomial hardness): DDH is hard in both `G₁` and `G₂` for PPT
distinguishers given the public parameters `pp n`. -/
def SXDH (G : BilinearGen) : Prop :=
  ∀ D : RandAlg (fun _ => List Bool × List Bool × List Bool) (fun _ => Bool), D.IsPPTAdv G.pp →
    Negligible (ddhAdv G.p G.rep₁ D) ∧ Negligible (ddhAdv G.p G.rep₂ D)

/-! ## Standard parameter regimes -/

/-- "Standard LWE" parameters: polynomial modulus `q`, polynomially many samples, Regev's
discretized Gaussian noise of rate `α` with `α q > 2√n` and inverse-polynomial `α < 1` (the
regime in which LWE is backed by Regev's worst-case reduction for `poly(n)` approximation
factors). -/
def StandardLWE (q : ℕ → ℕ+) (m : ℕ → ℕ) (α : ℕ → ℝ) : Prop :=
  PolyBounded (fun n => q n) ∧ PolyBounded m ∧
  (∃ P : Polynomial ℕ, ∀ n : ℕ, 1 / (((P.eval n : ℕ) : ℝ) + 1) ≤ α n) ∧ (∀ n, α n < 1) ∧
  (∀ n : ℕ, 2 * Real.sqrt (n : ℝ) < α n * ((q n : ℕ) : ℝ))

/-- "Standard LPN" parameters over a prime field `ZMod (p n)` of polynomial bit length:
polynomially many samples and noise rate `n^{-δ} ≤ τ n ≤ 1/2` for a constant `δ ∈ (0,1)`
(covers constant-noise binary LPN, `p = 2`, and the large-field LPN of Jain–Lin–Sahai). -/
def StandardLPN (p : ℕ → ℕ+) (m : ℕ → ℕ) (τ : ℕ → ℝ) : Prop :=
  (∀ n, (p n : ℕ).Prime) ∧ PolyBounded (fun n => Nat.log 2 (p n)) ∧ PolyBounded m ∧
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (-δ) ≤ τ n ∧ τ n ≤ 1 / 2

/-! ## #126: iO from polynomially hard standard assumptions -/

/-- **iO from standard polynomial assumptions** (OPEN; ProofAtlas #126, "Indistinguishability
Obfuscation from Constant-Degree Homomorphic Assumptions"). Exact statement:
*"Construct indistinguishability obfuscation based purely on standard polynomial-time
assumptions (such as standard LWE, LPN, and degree-2 multilinear pairings) without
sub-exponential loss."*

Formalization: for every efficient asymmetric bilinear group family `G` (with public
parameters `pp`), there are standard LWE parameters, standard LPN parameters and an obfuscator
`O` (PPT given `pp`, perfectly correct) such that polynomial hardness of decision LWE, of
decision LPN and of SXDH on `G` (all against PPT adversaries given `pp`) implies that `O` is
indistinguishable against all PPT distinguishers given `pp`.

Modelling simplifications (honest list):
* "standard polynomial-time assumptions (such as …)" is fixed to exactly three assumptions:
  decision LWE (`StandardLWE`), decision LPN over a prime field (`StandardLPN`) and SXDH; other
  "standard" assumptions are not allowed (the ProofAtlas list is open-ended);
* "without sub-exponential loss" is modelled by assuming only *polynomial* hardness (PPT
  adversaries, negligible advantage); the known constructions (Jain–Lin–Sahai STOC 2021,
  EUROCRYPT 2022) need sub-exponential hardness, which is not formalized here;
* the construction is an implication between hardness statements, not an explicit black-box
  reduction; the obfuscator may depend on `G` (and is quantified after it);
* circuits are straight-line NAND programs (`Circ`), the distinguisher is a uniform PPT machine
  given both circuits (this implies the usual sampler-with-auxiliary-input definition with the
  circuits as auxiliary input), and pairing groups are given by fixed public parameters `pp n`
  in the representation model (`BilinearGen`), instead of a randomized group generator; every
  party (obfuscator, distinguisher, LWE/LPN/DDH adversaries) receives `pp n`. This avoids
  requiring deterministic construction of large primes (an unrelated open problem); since the
  statement quantifies over *all* efficient `G`, a `G` whose `pp` carries extra information only
  adds cases and does not weaken the statement for real pairing families;
* there is no requirement that `O` uses `G`, LWE or LPN at all: any provably secure `O` would do.

NOT proved here. -/
def IOFromPolyStandardAssumptions : Prop :=
  ∀ G : BilinearGen, G.IsEfficient →
    ∃ (qL : ℕ → ℕ+) (mL : ℕ → ℕ) (α : ℕ → ℝ) (pP : ℕ → ℕ+) (mP : ℕ → ℕ) (τ : ℕ → ℝ)
      (O : Obfuscator),
      StandardLWE qL mL α ∧ StandardLPN pP mP τ ∧ O.IsPPTAdv G.pp ∧ O.Correct ∧
      (DecisionHardAdv G.pp qL mL (fun n => dGauss (qL n) (α n)) →
        DecisionHardAdv G.pp pP mP (fun n => fieldLPNNoise (pP n) (τ n)) →
        SXDH G → O.IsIndistAdv G.pp)

/-! ## Lattices and worst-case lattice problems -/

/-- A lattice basis in `ℤⁿ` (rows are basis vectors). -/
abbrev IntBasis (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-- The lattice `L(B) = {z B : z ∈ ℤⁿ}`. -/
def lattice {n : ℕ} (B : IntBasis n) : Set (Fin n → ℤ) := Set.range fun z => z ᵥ* B

/-- Euclidean norm of an integer vector. -/
noncomputable def norm2 {n : ℕ} (v : Fin n → ℤ) : ℝ := Real.sqrt (∑ i, ((v i : ℝ)) ^ 2)

/-- First successive minimum `λ₁(L(B))`. -/
noncomputable def lambda1 {n : ℕ} (B : IntBasis n) : ℝ := sInf (norm2 '' (lattice B \ {0}))

/-- `n`-th successive minimum `λₙ(L(B))`: least `r` such that `L(B)` contains `n` linearly
independent vectors of norm `≤ r`. -/
noncomputable def lambdaN {n : ℕ} (B : IntBasis n) : ℝ :=
  sInf {r : ℝ | ∃ V : Fin n → Fin n → ℤ, (∀ i, V i ∈ lattice B) ∧
    LinearIndependent ℚ (fun i j => (V i j : ℚ)) ∧ ∀ i, norm2 (V i) ≤ r}

/-- A randomized algorithm `alg` (with `c` coins, possibly failing with `none`) solves the
promise problem `GapSVP_γ` in dimension `n` with error `≤ 1/3`: on a full-rank basis `B` and a
threshold `d > 0`, it says yes if `λ₁ ≤ d` and no if `λ₁ > γ d`. -/
def SolvesGapSVP (γ : ℝ) (n c : ℕ) (alg : IntBasis n × ℚ → Word c → Option Bool) : Prop :=
  ∀ (B : IntBasis n) (d : ℚ), B.det ≠ 0 → 0 < d →
    (lambda1 B ≤ d → 2 / 3 ≤ probCoins c fun ω => alg (B, d) ω = some true) ∧
    (γ * d < lambda1 B → 2 / 3 ≤ probCoins c fun ω => alg (B, d) ω = some false)

/-- `alg` solves `SIVP_γ` in dimension `n` with probability `≥ 2/3`: it outputs `n` linearly
independent lattice vectors of norm `≤ γ λₙ`. -/
def SolvesSIVP (γ : ℝ) (n c : ℕ) (alg : IntBasis n → Word c → Option (Matrix (Fin n) (Fin n) ℤ)) :
    Prop :=
  ∀ B : IntBasis n, B.det ≠ 0 →
    2 / 3 ≤ probCoins c fun ω => ∃ V, alg B ω = some V ∧ (∀ i, V i ∈ lattice B) ∧
      LinearIndependent ℚ (fun i j => (V i j : ℚ)) ∧ ∀ i, norm2 (V i) ≤ γ * lambdaN B

/-- Oracle condition of Regev's theorem: `O` solves search LWE (dimension `n`, modulus `q`,
`m` samples, noise `χ`) for **every** secret with probability at least `1 - 2⁻ⁿ`. -/
def SolvesSearchLWE (q : ℕ+) (m n : ℕ) (χ : ZMod q → ℝ) (O : LWEInst q m n → (Fin n → ZMod q)) :
    Prop :=
  ∀ s, 1 - (1 / 2 : ℝ) ^ n ≤ searchSuccFixed q m n χ O s

/-! ## #232: classical worst-case reduction for LWE -/

/-- **Classical worst-case hardness for LWE subsuming Regev** (OPEN; ProofAtlas #232,
"Classical Worst-Case Hardness Reduction for LWE"). Exact statement: *"Determine whether there
is a classical (non-quantum) worst-case hardness reduction for the Learning With Errors problem
that fully subsumes Regev's quantum reduction, i.e. reducing both GapSVP_gamma and SIVP_gamma to
LWE for the same parameters, with polynomial modulus and no loss in lattice dimension."*

This `Prop` is the **positive** answer. For every polynomial modulus `q`, every noise rate
`α ∈ (0,1)` with `α q > 2√n` (Regev's hypotheses), there is a fixed polylogarithmic factor
`(log n)^c` such that for every polynomial number of samples `m` there are *classical* PPT
black-box oracle reductions that, for all large `n` and **every** (possibly inefficient) oracle
solving search LWE in dimension `n` (same dimension: no loss) with Regev's error distribution
`Ψ̄_α`, solve `GapSVP_γ` and `SIVP_γ` in dimension `n` for `γ = n (log n)^c / α`
(Regev's `Õ(n/α)`).

Known (not formalized): Regev 2005 gives this with a *quantum* reduction; Peikert 2009 gives a
classical reduction for GapSVP only and with exponential modulus; Brakerski–Langlois–Peikert–
Regev–Stehlé 2013 give a classical GapSVP reduction with polynomial modulus but with dimension
loss (`n` to about `n²`). None gives this statement.

Modelling simplifications: the reduction gets a deterministic oracle and chooses the oracle's
inputs (the oracle answers whole sample sets `(A, b)` of size `m`); the oracle hypothesis is
Regev's search form (search/decision and worst/average-secret equivalences are classical but not
formalized); `γ` uses `log(n+2)`; failure probability `1/3`. The negative answer is a black-box
separation and is not stated. NOT proved here. -/
def ClassicalLWEReductionExists : Prop :=
  ∀ (q : ℕ → ℕ+) (α : ℕ → ℝ), PolyBounded (fun n => q n) → (∀ n, 0 < α n ∧ α n < 1) →
    (∀ n : ℕ, 2 * Real.sqrt (n : ℝ) < α n * ((q n : ℕ) : ℝ)) →
    ∃ c : ℕ, ∀ m : ℕ → ℕ, PolyBounded m →
      (∃ R : OracleAlg (fun n => IntBasis n × ℚ) (fun n => LWEInst (q n) (m n) n)
          (fun n => Fin n → ZMod (q n)) (fun _ => Bool),
        R.IsPPT ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ O : LWEInst (q n) (m n) n → (Fin n → ZMod (q n)),
          SolvesSearchLWE (q n) (m n) n (dGauss (q n) (α n)) O →
          SolvesGapSVP ((n : ℝ) * Real.log ((n : ℝ) + 2) ^ c / α n) n (R.coins n)
            (fun x ω => R.run n x ω O)) ∧
      (∃ R : OracleAlg (fun n => IntBasis n) (fun n => LWEInst (q n) (m n) n)
          (fun n => Fin n → ZMod (q n)) (fun n => Matrix (Fin n) (Fin n) ℤ),
        R.IsPPT ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ O : LWEInst (q n) (m n) n → (Fin n → ZMod (q n)),
          SolvesSearchLWE (q n) (m n) n (dGauss (q n) (α n)) O →
          SolvesSIVP ((n : ℝ) * Real.log ((n : ℝ) + 2) ^ c / α n) n (R.coins n)
            (fun x ω => R.run n x ω O))

/-! ## #286: worst-case to average-case reduction for LPN -/

/-- Worst-case bounded-distance decoding for binary linear codes: `alg` solves `BDD_w` for codes
`G ∈ F₂^{n × N}` if, for every generator matrix whose code has minimum distance `> 2w` and every
target `t` within Hamming distance `w` of a codeword `x G`, it outputs `x` with probability
`≥ 2/3`. -/
def SolvesBDD (N w n c : ℕ) (alg : Matrix (Fin n) (Fin N) (ZMod 2) × (Fin N → ZMod 2) →
    Word c → Option (Fin n → ZMod 2)) : Prop :=
  ∀ (G : Matrix (Fin n) (Fin N) (ZMod 2)),
    (∀ x : Fin n → ZMod 2, x ≠ 0 → 2 * w < hammingNorm (x ᵥ* G)) →
    ∀ (x : Fin n → ZMod 2) (e : Fin N → ZMod 2), hammingNorm e ≤ w →
      2 / 3 ≤ probCoins c fun ω => alg (G, x ᵥ* G + e) ω = some x

/-- The repetition code: generator matrix `F₂^{n × n r}` repeating each message bit `r`
times (column `j` copies message bit `⌊j / r⌋`). -/
def repMat (n r : ℕ) : Matrix (Fin n) (Fin (n * r)) (ZMod 2) :=
  fun i j => if j.val / r = i.val then 1 else 0

lemma div_lt_of_fin_mul {n r : ℕ} (j : Fin (n * r)) : j.val / r < n := by
  have := j.isLt
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp at this
  · exact (Nat.div_lt_iff_lt_mul h).2 this

lemma repMat_vecMul (n r : ℕ) (x : Fin n → ZMod 2) (j : Fin (n * r)) :
    (x ᵥ* repMat n r) j = x ⟨j.val / r, div_lt_of_fin_mul j⟩ := by
  simp only [vecMul, dotProduct, repMat, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single_of_mem (⟨j.val / r, div_lt_of_fin_mul j⟩ : Fin n)
    (Finset.mem_univ _)]
  · simp
  · intro b _ hb
    exact ite_eq_right_iff.2 fun h => absurd (Fin.ext h.symm) hb

/-- Known result (folklore; e.g. MacWilliams–Sloane, *The Theory of Error-Correcting Codes*,
Ch. 1): the `r`-fold repetition code has minimum distance `≥ r`: every nonzero message gives a
codeword of Hamming weight at least `r`. -/
theorem repMat_dist (n r : ℕ) (x : Fin n → ZMod 2) (hx : x ≠ 0) :
    r ≤ hammingNorm (x ᵥ* repMat n r) := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push Not at hc; exact hx (funext hc)
  unfold hammingNorm
  have hinj : ∀ k : Fin r, i.val * r + k.val < n * r := fun k => by
    have := i.isLt; nlinarith [k.isLt]
  let f : Fin r → Fin (n * r) := fun k => ⟨i.val * r + k.val, hinj k⟩
  have hf : Function.Injective f := fun a b h => by
    simp only [f, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  calc r = (Finset.univ.map ⟨f, hf⟩).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at hj
      obtain ⟨k, rfl⟩ := hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [repMat_vecMul]
      have : (i.val * r + k.val) / r = i.val := by
        have hr : 0 < r := Nat.pos_of_ne_zero (fun h => by subst h; exact k.elim0)
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hr, Nat.div_eq_of_lt k.isLt, zero_add]
      convert hi

/-- Non-vacuity of `BDD_w` at code length `N`: for every dimension `n ≥ 1` there is a binary
linear code `F₂^{n × N(n)}` of minimum distance `> 2 w(n)`, so `SolvesBDD (N n) (w n) n` has
instances. (It implies `2 w(n) + 1 ≤ N(n)` for `n ≥ 1`.) -/
def BDDNonvacuous (N w : ℕ → ℕ) : Prop :=
  ∀ n, 1 ≤ n → ∃ G : Matrix (Fin n) (Fin (N n)) (ZMod 2),
    ∀ x : Fin n → ZMod 2, x ≠ 0 → 2 * w n < hammingNorm (x ᵥ* G)

/-- Known result (via the repetition code, `repMat_dist`): the parameter constraints of
`LPNWorstToAverageReductionExists` are jointly satisfiable, e.g. by `w(n) = ⌊log₂ n⌋` and
`N(n) = n (2 w(n) + 1)`. This only shows that the constraints are consistent; it says nothing
about the open problem. -/
theorem lpn_params_satisfiable :
    ∃ N w : ℕ → ℕ, PolyBounded N ∧ (∀ n, n ≤ N n) ∧ (∀ n, Nat.log 2 n ≤ w n) ∧
      BDDNonvacuous N w := by
  refine ⟨fun n => n * (2 * Nat.log 2 n + 1), fun n => Nat.log 2 n, ?_, ?_, fun n => le_rfl, ?_⟩
  · refine ⟨2 * Polynomial.X ^ 2 + Polynomial.X, fun n => ?_⟩
    have := Nat.log_le_self 2 n
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_ofNat]
    nlinarith
  · intro n; exact Nat.le_mul_of_pos_right n (by omega)
  · intro n _
    exact ⟨repMat n (2 * Nat.log 2 n + 1), fun x hx =>
      Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (repMat_dist _ _ x hx)⟩

/-- **Worst-case to average-case reduction for constant-noise LPN** (OPEN; ProofAtlas #286,
"Worst-case to average-case hardness reduction for LPN"). Exact statement: *"Decide whether
average-case hardness of Learning Parity with Noise in the standard constant-noise regime can be
established by a worst-case-to-average-case reduction from a worst-case decoding problem."*

This `Prop` is the **positive** answer for the worst-case decoding problem `BDD`
(`SolvesBDD`): there is a constant noise rate `τ ∈ (0, 1/2)`, a polynomial code length
`N(n) ≥ n` and a decoding radius `w(n) ≥ log₂ n`, for which `BDD_{w(n)}` in length `N(n)` has
instances in every dimension `n ≥ 1` (`BDDNonvacuous`), such that for every polynomial number of
samples `m` and every inverse-polynomial success bound `1/(P(n)+1)`, a PPT black-box oracle
reduction decodes every `BDD_{w(n)}` instance of dimension `n` given **any** (possibly
inefficient) oracle that solves search LPN (dimension `n`, `m` samples, Bernoulli(`τ`) noise)
with average success probability `≥ 1/(P(n)+1)`.

Modelling choices (honest list): the "worst-case decoding problem" is fixed to unique-decoding
BDD for arbitrary binary linear codes (Brakerski–Lyubashevsky–Vaikuntanathan–Wichs 2019 use
decoding of *balanced* codes; our problem is at least as hard). The radius condition
`w(n) ≥ log₂ n` excludes the regime `w = O(1)`, where BDD is solved in polynomial time by
exhaustive search over error patterns; this threshold is our modelling choice. The condition
`BDDNonvacuous N w` excludes parameters for which no code has minimum distance `> 2w` (e.g.
`w(n) ≥ N(n)/2`), where `SolvesBDD` would hold vacuously; `lpn_params_satisfiable` shows the
constraints are consistent. We do not rule out that some other admissible choice of `(N, w)`
makes BDD easy for a reason we have not noticed (e.g. radii so close to the maximum possible
distance that only very special codes qualify); beyond the two conditions above, the choice of
`(N, w)` is left to the reduction, as in the informal question.
To our knowledge the known reductions (BLVW 2019 and follow-ups) reach only noise rates tending
to `1/2` or to `0`,
not a constant. The negative answer (a black-box separation) is not stated. The oracle is
deterministic and the reduction picks its inputs. NOT proved here. -/
def LPNWorstToAverageReductionExists : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ τ < 1 / 2 ∧
    ∃ N w : ℕ → ℕ, PolyBounded N ∧ (∀ n, n ≤ N n) ∧ (∀ n, Nat.log 2 n ≤ w n) ∧
      BDDNonvacuous N w ∧ ∀ m : ℕ → ℕ, PolyBounded m → ∀ P : Polynomial ℕ,
        ∃ R : OracleAlg (fun n => Matrix (Fin n) (Fin (N n)) (ZMod 2) × (Fin (N n) → ZMod 2))
            (fun n => LWEInst 2 (m n) n) (fun n => Fin n → ZMod 2) (fun n => Fin n → ZMod 2),
          R.IsPPT ∧ ∀ n : ℕ, ∀ O : LWEInst 2 (m n) n → (Fin n → ZMod 2),
            1 / (((P.eval n : ℕ) : ℝ) + 1) ≤ searchSuccAvg 2 (m n) n (bernoulliNoise τ) O →
            SolvesBDD (N n) (w n) n (R.coins n) (fun x ω => R.run n x ω O)

/-! ## Axiom checks -/

#print axioms noiseless_exists_left_inverse
#print axioms noiseless_recover
#print axioms noiseless_secret_unique
#print axioms lwe_zero_noise_distinguishable
#print axioms lwe_zero_noise_distinguishable_half
#print axioms truthTable_correct
#print axioms truthTable_eq_of_equiv
#print axioms truthTable_adv_zero
#print axioms truthTable_length_le
#print axioms repMat_dist
#print axioms lpn_params_satisfiable

end CryptoLean.OpenProblems.CryptoAssumptions
