import Mathlib
import CryptoLean.OpenProblems.CommComplexity

/-!
# Quantum versus classical communication complexity of total functions

Open problem (ProofAtlas, edition 2026-11-12):
* #212 Quantum versus Classical Communication Complexity of Total Functions
  -> `RandomizedPolyInQuantumConjecture` (OPEN, `def ... : Prop`).

The problem is **not** resolved here, and nothing in this file bears on the
randomized-versus-*quantum* question. What is proved are known *classical* facts:

* `randCC_le_detCC` (known, trivial; Kushilevitz–Nisan, *Communication Complexity*, 1997, Ch. 3):
  `R(f) ≤ D(f)`;
* `le_detCC_EQ` (known; Yao 1979, via the log-rank bound of Mehlhorn–Schmidt 1982):
  `n ≤ D(EQ_n)`, since the communication matrix of `EQ_n` is the `2ⁿ × 2ⁿ` identity;
* `detCC_EQ_le` (known, trivial protocol): `D(EQ_n) ≤ n + 1`;
* `eqHashProtocol_error` / `randCC_EQ_le` (known; Yao 1979, Kushilevitz–Nisan Ch. 3):
  the public-coin protocol that compares two random inner products over `𝔽₂` has
  cost `3` and error exactly `1/4` on every pair `x ≠ y` (and `0` when `x = y`), so
  `R(EQ_n) ≤ 3`;
* `EQ_separation`: the resulting exponential gap between `D` and `R` for a total function.

## Model

* Deterministic protocols, `detCC` and `boolMatrix` are reused from
  `CryptoLean.OpenProblems.CommComplexity`.
* A **public-coin randomized protocol** (`RandProtocol`) is a finite probability distribution
  `w` on a finite set `R` of random strings together with a deterministic protocol `P r` for each
  `r`. Its cost is the maximum depth of the `P r`; its error on `(x, y)` is the `w`-weight of the
  `r` with `(P r).eval x y ≠ f x y`. `randCC f` is the least cost with error `≤ 1/3` on every
  input (two-sided bounded error, Kushilevitz–Nisan Def. 3.1–3.3). Finite support loses nothing
  for finite input sets of a fixed cost (there are finitely many protocol trees up to
  behaviour), and arbitrary real weights are allowed.
* A **quantum protocol** (`QProtocol`, Yao 1993 / Kremer 1995 model, **no prior entanglement**)
  acts on `ℂ^{A ⊗ C ⊗ B}`: Alice's private register `A` (any finite dimension), a one-qubit
  channel `C`, and Bob's private register `B`. It starts in the basis state `|0,0,0⟩`. In round
  `j` (`j = 0, …, rounds - 1`) the owner of the channel applies a unitary on its private register
  and the channel that depends on its own input and on `j` — Alice on `A ⊗ C` in even rounds, Bob
  on `C ⊗ B` in odd rounds — and then sends the channel qubit to the other party. So exactly one
  qubit is communicated per round and the cost is `rounds`. We require `rounds` to be odd, so that
  Bob holds the channel at the end; Bob then applies a final local unitary on `C ⊗ B` depending
  on `y` and measures `C ⊗ B` in the computational basis, outputting `accept` of the outcome.
  The protocol computes `f` with error `ε` if on every input the probability of the wrong output
  is `≤ ε`.

### Modelling simplifications (honest list)

1. **One qubit per round, strict alternation, Alice first, odd number of rounds.** A general
   protocol sending `q` qubits in messages of arbitrary length is simulated in this model with at
   most `2q + 2` rounds (insert identity rounds), and conversely; this affects costs only by a
   constant factor and an additive constant, which is irrelevant for a *polynomial* relation.
2. **No shared entanglement** (`Q(f)` of Yao, not `Q*(f)` of Cleve–Buhrman). The atlas statement
   speaks of "bounded-error quantum communication complexity" without entanglement qualifier; the
   entanglement-assisted variant would be a (formally stronger) different statement, not stated.
3. **Public-coin** randomized complexity. Private-coin `R` exceeds public-coin `R` by at most an
   additive `O(log log |X×Y|)` (Newman 1991); we state the public-coin version.
4. Bounded error is the constant `1/3` for both models (any constant in `(0, 1/2)` gives the same
   complexity up to constant factors by amplification, so the polynomial question is unchanged).
5. "Bounded by a polynomial" is rendered as `R(f) ≤ C · (q + 1)^C` for a natural constant `C`,
   which is equivalent to `R(f) ≤ p(Q(f))` for some polynomial `p` with natural coefficients.
   Instead of defining `Q(f)` as a minimum (whose existence for every `f` would need a classical
   simulation argument that we do not formalize), the conjecture quantifies over every quantum
   protocol for `f` and bounds `R(f)` by a polynomial in *its* cost; this is equivalent.
6. Input sets are arbitrary finite types in universe `Type` (only their size matters); complex
   amplitudes and exact unitaries (Mathlib's `Matrix.unitaryGroup`) are used.

`trivialQProtocol_computes` checks the quantum model is inhabited (a one-round protocol computes
any constant function with zero error), so the hypothesis of the conjecture is satisfiable.
-/

namespace CryptoLean.OpenProblems.QuantumCC

open CryptoLean.OpenProblems.CommComplexity Protocol Matrix
open scoped Kronecker

universe u v

/-! ## Public-coin randomized protocols -/

/-- A public-coin randomized protocol: a probability distribution `w` on a finite set `R` of
random strings and a deterministic protocol `P r` for each random string `r`. -/
structure RandProtocol (X : Type u) (Y : Type v) where
  /-- The (finite) set of random strings. -/
  R : Type
  [fin : Fintype R]
  /-- Probability weights of the random strings. -/
  w : R → ℝ
  w_nonneg : ∀ r, 0 ≤ w r
  w_sum : ∑ r, w r = 1
  /-- The deterministic protocol used for random string `r`. -/
  P : R → Protocol X Y

attribute [instance] RandProtocol.fin

namespace RandProtocol

variable {X : Type u} {Y : Type v}

/-- Worst-case cost: the maximum depth over all random strings. -/
def cost (RP : RandProtocol X Y) : ℕ :=
  Finset.univ.sup fun r => (RP.P r).depth

/-- Error probability of `RP` on input `(x, y)` with respect to `f`. -/
noncomputable def errorProb (RP : RandProtocol X Y) (f : X → Y → Bool) (x : X) (y : Y) : ℝ :=
  ∑ r, if (RP.P r).eval x y = f x y then 0 else RP.w r

/-- `RP` computes `f` with (two-sided) error at most `ε` on every input. -/
def Computes (RP : RandProtocol X Y) (f : X → Y → Bool) (ε : ℝ) : Prop :=
  ∀ x y, RP.errorProb f x y ≤ ε

/-- A deterministic protocol as a randomized one (one random string of weight 1). -/
def ofDet (P : Protocol X Y) : RandProtocol X Y where
  R := Unit
  w := fun _ => 1
  w_nonneg := fun _ => zero_le_one
  w_sum := by simp
  P := fun _ => P

theorem cost_ofDet (P : Protocol X Y) : (ofDet P).cost = P.depth := by
  simp only [cost, ofDet]
  exact Finset.sup_const Finset.univ_nonempty _

theorem computes_ofDet {P : Protocol X Y} {f : X → Y → Bool} (hP : P.Computes f) :
    (ofDet P).Computes f 0 := by
  intro x y
  simp [errorProb, ofDet, hP x y]

end RandProtocol

open RandProtocol

variable {X : Type u} {Y : Type v}

theorem exists_randProtocol_cost [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    ∃ d : ℕ, ∃ RP : RandProtocol X Y, RP.Computes f (1 / 3) ∧ RP.cost ≤ d := by
  obtain ⟨P, hP, -⟩ := detCC_spec f
  refine ⟨P.depth, ofDet P, fun x y => (computes_ofDet hP x y).trans (by norm_num), ?_⟩
  rw [cost_ofDet]

/-- Public-coin bounded-error randomized communication complexity `R(f)`: the least cost of a
public-coin protocol computing `f` with error at most `1/3` on every input. -/
noncomputable def randCC [Fintype X] [Fintype Y] (f : X → Y → Bool) : ℕ := by
  classical
  exact Nat.find (exists_randProtocol_cost f)

theorem randCC_le [Fintype X] [Fintype Y] {f : X → Y → Bool} {RP : RandProtocol X Y}
    (hRP : RP.Computes f (1 / 3)) : randCC f ≤ RP.cost := by
  classical
  unfold randCC
  convert Nat.find_min' (exists_randProtocol_cost f) ⟨RP, hRP, le_rfl⟩

/-- **Known result** (trivial; Kushilevitz–Nisan, *Communication Complexity*, 1997, Ch. 3):
`R(f) ≤ D(f)` — a deterministic protocol is a randomized one with zero error. -/
theorem randCC_le_detCC [Fintype X] [Fintype Y] (f : X → Y → Bool) :
    randCC f ≤ detCC f := by
  obtain ⟨P, hP, hd⟩ := detCC_spec f
  refine (randCC_le (RP := ofDet P) fun x y => ?_).trans ?_
  · exact (computes_ofDet hP x y).trans (by norm_num)
  · rw [cost_ofDet]; exact hd

/-! ## Equality: deterministic versus randomized -/

/-- The equality function `EQ_n` on `n`-bit strings, with `{0,1}ⁿ` identified with `𝔽₂ⁿ`. -/
def EQ (n : ℕ) : (Fin n → ZMod 2) → (Fin n → ZMod 2) → Bool :=
  fun x y => decide (x = y)

theorem boolMatrix_EQ (n : ℕ) : boolMatrix (EQ n) = 1 := by
  ext x y
  simp [boolMatrix, EQ, Matrix.one_apply]

/-- **Known result** (Yao 1979; via the log-rank bound of Mehlhorn–Schmidt 1982,
Kushilevitz–Nisan Ch. 1): `n ≤ D(EQ_n)`, since `M_{EQ_n}` is the `2ⁿ × 2ⁿ` identity matrix,
of rank `2ⁿ`. -/
theorem le_detCC_EQ (n : ℕ) : n ≤ detCC (EQ n) := by
  have h := clog_rank_le_detCC (EQ n)
  rwa [boolMatrix_EQ, Matrix.rank_one, Fintype.card_fun, ZMod.card, Fintype.card_fin,
    Nat.clog_pow _ _ (by norm_num)] at h

private theorem zmod2_eq_of_decide {a b : ZMod 2} (h : decide (a = 1) = decide (b = 1)) :
    a = b := by
  revert a b; decide

/-- **Known result** (trivial protocol; Kushilevitz–Nisan Ch. 1): `D(EQ_n) ≤ n + 1` — Alice
sends her `n` bits and Bob announces the answer. -/
theorem detCC_EQ_le (n : ℕ) : detCC (EQ n) ≤ n + 1 := by
  let P : Protocol (Fin n → ZMod 2) (Fin n → ZMod 2) :=
    sendThenBob n (fun x i => decide (x i = 1)) fun w y => decide (w = fun i => decide (y i = 1))
  have hP : P.Computes (EQ n) := by
    intro x y
    simp only [P, eval_sendThenBob, EQ]
    congr 1
    apply propext
    constructor
    · intro h; funext i; exact zmod2_eq_of_decide (congrFun h i)
    · rintro rfl; rfl
  calc detCC (EQ n) ≤ P.depth := detCC_le hP
    _ = n + 1 := depth_sendThenBob _ _ _

/-- For a nonzero `z ∈ 𝔽₂ⁿ`, exactly half of all `v ∈ 𝔽₂ⁿ` satisfy `z ⬝ v = 0`. -/
theorem two_mul_card_dot_eq_zero {n : ℕ} {z : Fin n → ZMod 2} (hz : z ≠ 0) :
    2 * (Finset.univ.filter fun v : Fin n → ZMod 2 => z ⬝ᵥ v = 0).card = 2 ^ n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push Not at h; exact hz (funext h)
  have hi1 : z i = 1 := by revert hi; generalize z i = a; revert a; decide
  have hne : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  let τ : (Fin n → ZMod 2) → (Fin n → ZMod 2) := fun v => v + Pi.single i 1
  have hτ : ∀ v, z ⬝ᵥ τ v = z ⬝ᵥ v + 1 := by
    intro v; simp [τ, dotProduct_add, hi1]
  have hττ : ∀ v, τ (τ v) = v := by
    intro v; simp only [τ, add_assoc]
    have : (Pi.single i 1 + Pi.single i 1 : Fin n → ZMod 2) = 0 := by
      rw [← Pi.single_add]; simp; decide
    rw [this, add_zero]
  have hcard : (Finset.univ.filter fun v : Fin n → ZMod 2 => z ⬝ᵥ v = 0).card
      = (Finset.univ.filter fun v : Fin n → ZMod 2 => ¬ z ⬝ᵥ v = 0).card := by
    refine Finset.card_bij' (fun v _ => τ v) (fun v _ => τ v) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hτ, hv]; decide
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [hτ, hne _ hv]; decide
    · intro v _; exact hττ v
    · intro v _; exact hττ v
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → ZMod 2))) (fun v => z ⬝ᵥ v = 0)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  omega

/-- The public-coin hashing protocol for `EQ_n` (Yao 1979; Kushilevitz–Nisan Ch. 3): the
public random string is a pair `r = (r₀, r₁)` of uniformly random vectors in `𝔽₂ⁿ`; Alice sends
the two bits `⟨x, r₀⟩, ⟨x, r₁⟩` and Bob outputs whether they equal `⟨y, r₀⟩, ⟨y, r₁⟩`. -/
noncomputable def eqHashProtocol (n : ℕ) : RandProtocol (Fin n → ZMod 2) (Fin n → ZMod 2) where
  R := Fin 2 → Fin n → ZMod 2
  w := fun _ => 1 / (Fintype.card (Fin 2 → Fin n → ZMod 2) : ℝ)
  w_nonneg := fun _ => by positivity
  w_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  P := fun r => sendThenBob 2 (fun x i => decide (x ⬝ᵥ r i = 1))
    fun w y => decide (w = fun i => decide (y ⬝ᵥ r i = 1))

theorem eqHashProtocol_cost (n : ℕ) : (eqHashProtocol n).cost = 3 := by
  simp only [cost, eqHashProtocol, depth_sendThenBob]
  exact Finset.sup_const Finset.univ_nonempty _

theorem eqHashProtocol_eval (n : ℕ) (r : Fin 2 → Fin n → ZMod 2) (x y : Fin n → ZMod 2) :
    ((eqHashProtocol n).P r).eval x y = decide (∀ i, (x - y) ⬝ᵥ r i = 0) := by
  simp only [eqHashProtocol, eval_sendThenBob]
  congr 1
  apply propext
  simp only [sub_dotProduct, sub_eq_zero]
  constructor
  · intro h i; exact zmod2_eq_of_decide (congrFun h i)
  · intro h; funext i; rw [h i]

/-- **Known result** (Yao 1979; Kushilevitz–Nisan, *Communication Complexity*, Ch. 3): the
random inner-product hashing protocol for `EQ_n` errs with probability exactly `1/4` on every
pair `x ≠ y` and never errs when `x = y`. -/
theorem eqHashProtocol_error (n : ℕ) (x y : Fin n → ZMod 2) :
    (eqHashProtocol n).errorProb (EQ n) x y = if x = y then 0 else 1 / 4 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, errorProb]
    refine Finset.sum_eq_zero fun (r : Fin 2 → Fin n → ZMod 2) _ => ?_
    have h : ((eqHashProtocol n).P r).eval x x = EQ n x x := by
      rw [eqHashProtocol_eval]; simp [EQ]
    simp only [h, ↓reduceIte]
  · simp only [hxy, ↓reduceIte]
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    set A := (Finset.univ.filter fun v : Fin n → ZMod 2 => (x - y) ⬝ᵥ v = 0) with hA
    have hA2 := two_mul_card_dot_eq_zero hz
    rw [← hA] at hA2
    have hwrong : ∀ r : Fin 2 → Fin n → ZMod 2,
        ((eqHashProtocol n).P r).eval x y = EQ n x y ↔ r ∉ Fintype.piFinset fun _ => A := by
      intro r
      rw [eqHashProtocol_eval]
      simp [EQ, hxy, Fintype.mem_piFinset, hA]
    have hsum : (eqHashProtocol n).errorProb (EQ n) x y
        = ∑ r : Fin 2 → Fin n → ZMod 2, if r ∈ Fintype.piFinset (fun _ => A)
            then 1 / (Fintype.card (Fin 2 → Fin n → ZMod 2) : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun (r : Fin 2 → Fin n → ZMod 2) _ => ?_
      have := hwrong r
      split_ifs <;> first | rfl | tauto
    rw [hsum, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Fintype.card_piFinset,
      nsmul_eq_mul]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fun, ZMod.card]
    have h2 : ((2 : ℝ) ^ n) = 2 * (A.card : ℝ) := by exact_mod_cast hA2.symm
    push_cast
    rw [h2]
    have hpos : (0 : ℝ) < A.card := by
      have : (0 : ℝ) < 2 ^ n := by positivity
      linarith
    field_simp
    ring

/-- **Known result** (Yao 1979): `R(EQ_n) ≤ 3` for every `n`. -/
theorem randCC_EQ_le (n : ℕ) : randCC (EQ n) ≤ 3 := by
  refine (randCC_le (RP := eqHashProtocol n) fun x y => ?_).trans (eqHashProtocol_cost n).le
  rw [eqHashProtocol_error]
  split_ifs <;> norm_num

/-- **Known result** (Yao 1979; Kushilevitz–Nisan Ch. 3): an exponential separation between
deterministic and public-coin randomized complexity for the *total* function `EQ_n`:
`n ≤ D(EQ_n) ≤ n + 1` while `R(EQ_n) ≤ 3`. (This is the classical D-vs-R gap; it says nothing
about the open randomized-vs-quantum question below.) -/
theorem EQ_separation (n : ℕ) :
    n ≤ detCC (EQ n) ∧ detCC (EQ n) ≤ n + 1 ∧ randCC (EQ n) ≤ 3 :=
  ⟨le_detCC_EQ n, detCC_EQ_le n, randCC_EQ_le n⟩

/-! ## Quantum protocols (Yao's model, no prior entanglement) -/

/-- Basis index of the global register `A ⊗ C ⊗ B`: Alice's register (dimension `a + 1`), the
one-qubit channel, Bob's register (dimension `b + 1`). -/
abbrev QIdx (a b : ℕ) := Fin (a + 1) × Fin 2 × Fin (b + 1)

/-- A quantum two-party protocol in Yao's model: Alice's and Bob's local unitaries per round
(depending on their own input and the round number) and Bob's final local unitary and
computational-basis acceptance predicate on `C ⊗ B`. See the module docstring. -/
structure QProtocol (X : Type u) (Y : Type v) where
  /-- Alice's private register has dimension `a + 1`. -/
  a : ℕ
  /-- Bob's private register has dimension `b + 1`. -/
  b : ℕ
  /-- Number of rounds = number of qubits communicated. -/
  rounds : ℕ
  /-- Alice's unitary on `A ⊗ C` in (even) round `j`, depending on `x`. -/
  alice : ℕ → X → Matrix.unitaryGroup (Fin (a + 1) × Fin 2) ℂ
  /-- Bob's unitary on `C ⊗ B` in (odd) round `j`, depending on `y`. -/
  bob : ℕ → Y → Matrix.unitaryGroup (Fin 2 × Fin (b + 1)) ℂ
  /-- Bob's final local unitary on `C ⊗ B` before measuring, depending on `y`. -/
  final : Y → Matrix.unitaryGroup (Fin 2 × Fin (b + 1)) ℂ
  /-- Output as a function of the computational-basis outcome on `C ⊗ B`. -/
  accept : Fin 2 × Fin (b + 1) → Bool

namespace QProtocol

/-- `U ⊗ 1_B` acting on `A ⊗ C ⊗ B`. -/
def aliceOp {a b : ℕ} (U : Matrix (Fin (a + 1) × Fin 2) (Fin (a + 1) × Fin 2) ℂ) :
    Matrix (QIdx a b) (QIdx a b) ℂ :=
  (U ⊗ₖ (1 : Matrix (Fin (b + 1)) (Fin (b + 1)) ℂ)).submatrix
    (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm

/-- `1_A ⊗ V` acting on `A ⊗ C ⊗ B`. -/
def bobOp {a b : ℕ} (V : Matrix (Fin 2 × Fin (b + 1)) (Fin 2 × Fin (b + 1)) ℂ) :
    Matrix (QIdx a b) (QIdx a b) ℂ :=
  (1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℂ) ⊗ₖ V

variable {X : Type u} {Y : Type v}

/-- The global operator of round `j`: Alice's in even rounds, Bob's in odd rounds. -/
noncomputable def roundOp (P : QProtocol X Y) (j : ℕ) (x : X) (y : Y) :
    Matrix (QIdx P.a P.b) (QIdx P.a P.b) ℂ :=
  if Even j then aliceOp (P.alice j x : Matrix _ _ ℂ) else bobOp (P.bob j y : Matrix _ _ ℂ)

/-- The state after all rounds and Bob's final unitary, starting from `|0,0,0⟩`. -/
noncomputable def finalState (P : QProtocol X Y) (x : X) (y : Y) : QIdx P.a P.b → ℂ :=
  (bobOp (P.final y : Matrix _ _ ℂ)).mulVec
    ((List.range P.rounds).foldl (fun v j => (P.roundOp j x y).mulVec v) (Pi.single 0 1))

/-- Probability that Bob's computational-basis measurement of `C ⊗ B` gives an accepted
outcome (Born rule, marginalising over Alice's register). -/
noncomputable def acceptProb (P : QProtocol X Y) (x : X) (y : Y) : ℝ :=
  ∑ t : QIdx P.a P.b, if P.accept t.2 then ‖P.finalState x y t‖ ^ 2 else 0

/-- `P` computes `f` with bounded error `ε`: an odd number of rounds (so Bob holds the channel
at the end) and wrong-output probability at most `ε` on every input. -/
def Computes (P : QProtocol X Y) (f : X → Y → Bool) (ε : ℝ) : Prop :=
  Odd P.rounds ∧ ∀ x y, (if f x y then 1 - P.acceptProb x y else P.acceptProb x y) ≤ ε

/-- The one-round protocol that does nothing and outputs the constant `c`. -/
def trivial (X : Type u) (Y : Type v) (c : Bool) : QProtocol X Y where
  a := 0
  b := 0
  rounds := 1
  alice := fun _ _ => 1
  bob := fun _ _ => 1
  final := fun _ => 1
  accept := fun _ => c

/-- Sanity check of the model: a constant function is computed with zero error by a one-qubit
protocol, so the hypothesis of the conjecture is satisfiable. -/
theorem trivialQProtocol_computes (c : Bool) :
    (trivial X Y c).Computes (fun _ _ => c) 0 := by
  refine ⟨⟨0, rfl⟩, fun x y => ?_⟩
  have hA : aliceOp (a := 0) (b := 0) (1 : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ) = 1 := by
    simp [aliceOp, submatrix_one_equiv]
  have hB : bobOp (a := 0) (b := 0) (1 : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) = 1 := by
    simp [bobOp]
  have hstate : (trivial X Y c).finalState x y = Pi.single 0 1 := by
    simp [finalState, roundOp, trivial, hA, hB]
    erw [Matrix.one_mulVec, Matrix.one_mulVec]
  have hsum : ∑ t : QIdx 0 0, ‖(Pi.single 0 1 : QIdx 0 0 → ℂ) t‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t _ ht; simp [ht]
    · simp
  unfold acceptProb
  rw [hstate]
  cases c
  · simp [trivial]
  · simp only [trivial, ↓reduceIte]
    exact (sub_nonpos.mpr (le_of_eq hsum.symm))

end QProtocol

/-! ## The open problem -/

/-- **Quantum versus classical communication complexity of total functions.**
OPEN — not proved here, and nothing in this file bears on it.

ProofAtlas exact statement (#212): "Prove that for every total Boolean function in the two-party
communication model, its bounded-error randomized communication complexity is bounded by a
polynomial in its bounded-error quantum communication complexity."

Formalisation: there is a constant `C` such that for every finite `X`, `Y`, every total
`f : X → Y → Bool` and every quantum protocol `P` (Yao's model, `QProtocol`) computing `f` with
error `≤ 1/3`, the public-coin randomized complexity satisfies `R(f) ≤ C · (cost P + 1)^C`.
Quantifying over all `P` is equivalent to bounding `R(f)` by a polynomial in
`Q(f) = min cost P`.

Modelling simplifications (see the module docstring for details): one qubit per round with
strict alternation, Alice first and an odd number of rounds (changes `Q` by a constant factor
plus an additive constant); no prior entanglement (`Q`, not `Q*`); public-coin `R`; error `1/3`
for both models; polynomial written as `C · (q+1)^C` with `C : ℕ`; inputs in universe `Type`.
The known separation `EQ_separation` (deterministic vs randomized) does **not** touch this
randomized-vs-quantum question. -/
def RandomizedPolyInQuantumConjecture : Prop :=
  ∃ C : ℕ, ∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool) (P : QProtocol X Y),
    P.Computes f (1 / 3) → randCC f ≤ C * (P.rounds + 1) ^ C

end CryptoLean.OpenProblems.QuantumCC

#print axioms CryptoLean.OpenProblems.QuantumCC.randCC_le_detCC
#print axioms CryptoLean.OpenProblems.QuantumCC.le_detCC_EQ
#print axioms CryptoLean.OpenProblems.QuantumCC.detCC_EQ_le
#print axioms CryptoLean.OpenProblems.QuantumCC.two_mul_card_dot_eq_zero
#print axioms CryptoLean.OpenProblems.QuantumCC.eqHashProtocol_error
#print axioms CryptoLean.OpenProblems.QuantumCC.randCC_EQ_le
#print axioms CryptoLean.OpenProblems.QuantumCC.EQ_separation
#print axioms CryptoLean.OpenProblems.QuantumCC.QProtocol.trivialQProtocol_computes
