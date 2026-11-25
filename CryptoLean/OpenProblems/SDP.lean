import Mathlib
import CryptoLean.OpenProblems.OneWay

/-!
# Semidefinite programming feasibility in the bit model

Open problem (ProofAtlas, edition 2026-11-12):
* #223 Polynomial-Time Decidability of Semidefinite Programming Feasibility
  -> `SDPFeasibilityInP` (OPEN, `def ... : Prop`). The open question is to *determine whether*
  this proposition holds; neither it nor its negation is proved here.

What is proved here are standard, known facts:
* `posSemidef_two_iff`: a real symmetric `2 × 2` matrix `[[a, b], [b, c]]` is positive
  semidefinite iff `a ≥ 0`, `c ≥ 0` and `b² ≤ a c`;
* `posSemidef_blockDiagonal`: a block-diagonal matrix with positive semidefinite blocks is
  positive semidefinite;
* the **Khachiyan / Ramana / Porkolab–Khachiyan size obstruction** (`khachiyan_lower_bound`,
  `khachiyan_feasible`, `khachiyan_num_lower_bound`): for every `n` there is an SDP feasibility
  instance with `n + 1` variables, matrices of size `2(n + 1)` and all entries in
  `{0, 1, 2}`, which is feasible, but every feasible point has `x_j ≥ 2^(2^j)` for all `j`.
  In particular every *rational* feasible point has a coordinate whose numerator is at least
  `2^(2^n)`, i.e. needs at least `2^n` bits, so a feasible point cannot in general be
  written down in polynomial time. This is why the ellipsoid / interior-point methods only
  give approximate (`ε`-feasibility) algorithms, and why exact SDP feasibility is not known to
  be in P (nor even in NP; Ramana 1997 shows it is in NP iff it is in co-NP).

## Model

* An instance consists of rational `k × k` matrices `A₀, A₁, …, A_m` (the
  `SDPInstance.Symmetric` predicate requires them to be symmetric). It is feasible iff there
  is a *real* `x ∈ ℝ^m` with `A₀ + Σ xᵢ Aᵢ ⪰ 0` (Mathlib `Matrix.PosSemidef` over `ℝ`).
* Polynomial time is the TM2 model of `CryptoLean.OpenProblems.OneWay` (`OneWay.InP`, over
  Mathlib's `Turing.TM2ComputableInPolyTime`) on bit strings `List Bool`.
* Instances are encoded concretely by `SDPInstance.encode`: natural numbers in binary
  (little-endian `Nat.bits`, each bit `b` written as `true, b`, terminated by `false`, so the
  code is self-delimiting and of length `2·⌈log₂(n+1)⌉ + 1`), integers as a sign bit followed
  by the absolute value, rationals as reduced numerator and denominator, and an instance as
  `k`, `m`, then all `(m+1)·k²` entries in order. Its length is polynomial in the usual bit
  size of the instance, which is what "polynomial time in the Turing bit model" refers to.

Modelling simplifications (stated honestly):
* the language `SDPFeasibilityLang` consists of encodings of *symmetric* feasible instances;
  strings that are not such encodings are outside the language, so a decider must also reject
  malformed input (which is easy in polynomial time with any reasonable encoding);
* the injectivity of `SDPInstance.encode` is not proved in Lean (it holds since the code is
  self-delimiting); the statement does not depend on it, since membership is defined
  existentially over instances with that code;
* the dense encoding of the matrices is used; it is polynomially equivalent to the other
  standard encodings, so the question is the same.
-/

namespace CryptoLean.OpenProblems.SDP

open Matrix

/-! ## The `2 × 2` positive semidefiniteness criterion and block-diagonal matrices -/

/-- Known result (e.g. Horn–Johnson, *Matrix Analysis*, 2nd ed., §7.1 / Sylvester's criterion
for semidefinite matrices in dimension 2): a real symmetric `2 × 2` matrix `[[a, b], [b, c]]`
is positive semidefinite iff `a ≥ 0`, `c ≥ 0` and `b² ≤ a c`. -/
theorem posSemidef_two_iff (a b c : ℝ) :
    (!![a, b; b, c]).PosSemidef ↔ 0 ≤ a ∧ 0 ≤ c ∧ b ^ 2 ≤ a * c := by
  constructor
  · intro h
    have h0 := h.diag_nonneg (i := 0)
    have h1 := h.diag_nonneg (i := 1)
    have hd := h.det_nonneg
    simp [Matrix.det_fin_two_of] at h0 h1 hd
    exact ⟨h0, h1, by nlinarith⟩
  · rintro ⟨ha, hc, hb⟩
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · simp only [dotProduct, mulVec, Fin.sum_univ_two, star_trivial]
      simp
      rcases ha.lt_or_eq with ha | ha
      · have : 0 ≤ a * (v 0 * (a * v 0 + b * v 1) + v 1 * (b * v 0 + c * v 1)) := by
          nlinarith [sq_nonneg (a * v 0 + b * v 1), sq_nonneg (v 1)]
        exact nonneg_of_mul_nonneg_right (by linarith) ha
      · subst ha
        have hb0 : b = 0 := by nlinarith [sq_nonneg b]
        subst hb0
        nlinarith [sq_nonneg (v 1)]

/-- Known result (standard; e.g. Horn–Johnson, *Matrix Analysis*, Obs. 7.1.2): a
block-diagonal real matrix whose diagonal blocks are positive semidefinite is positive
semidefinite. -/
theorem posSemidef_blockDiagonal {m o : Type*} [Fintype m] [Fintype o] [DecidableEq m]
    [DecidableEq o] (M : o → Matrix m m ℝ) (h : ∀ j, (M j).PosSemidef) :
    (blockDiagonal M).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
  · rw [IsHermitian, blockDiagonal_conjTranspose]
    congr 1; funext j; exact (h j).1
  · have : star v ⬝ᵥ (blockDiagonal M *ᵥ v) =
        ∑ j, star (fun i => v (i, j)) ⬝ᵥ (M j *ᵥ fun i => v (i, j)) := by
      simp only [dotProduct, mulVec, Fintype.sum_prod_type, blockDiagonal_apply, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [Finset.sum_comm]
      simp [ite_mul]
    rw [this]
    exact Finset.sum_nonneg fun j _ => (h j).dotProduct_mulVec_nonneg _

/-! ## Linear matrix inequalities -/

/-- The affine matrix pencil `A₀ + Σᵢ xᵢ Aᵢ` (rational data, real variables). -/
noncomputable def pencil {ι : Type*} [Fintype ι] {m : ℕ} (A₀ : Matrix ι ι ℚ)
    (A : Fin m → Matrix ι ι ℚ) (x : Fin m → ℝ) : Matrix ι ι ℝ :=
  A₀.map (Rat.cast : ℚ → ℝ) + ∑ i, x i • (A i).map (Rat.cast : ℚ → ℝ)

lemma pencil_apply {ι : Type*} [Fintype ι] {m : ℕ} (A₀ : Matrix ι ι ℚ)
    (A : Fin m → Matrix ι ι ℚ) (x : Fin m → ℝ) (r s : ι) :
    pencil A₀ A x r s = (A₀ r s : ℝ) + ∑ i, x i * (A i r s : ℝ) := by
  simp [pencil, Matrix.sum_apply]

lemma pencil_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ} (A₀ : Matrix ι ι ℚ)
    (A : Fin m → Matrix ι ι ℚ) (x : Fin m → ℝ) (f : κ → ι) :
    pencil (A₀.submatrix f f) (fun i => (A i).submatrix f f) x =
      (pencil A₀ A x).submatrix f f := by
  ext r s; simp [pencil_apply]

lemma pencil_blockDiagonal {μ o : Type*} [Fintype μ] [Fintype o] [DecidableEq o] {m : ℕ}
    (B₀ : o → Matrix μ μ ℚ) (B : Fin m → o → Matrix μ μ ℚ) (x : Fin m → ℝ) :
    pencil (blockDiagonal B₀) (fun i => blockDiagonal (B i)) x =
      blockDiagonal (fun j => pencil (B₀ j) (fun i => B i j) x) := by
  ext ⟨r, j⟩ ⟨s, j'⟩
  simp only [pencil_apply, blockDiagonal_apply]
  split_ifs <;> simp

/-! ## SDP feasibility instances and the decision problem -/

/-- An SDP feasibility instance: rational `k × k` matrices `A 0, A 1, …, A m`. -/
structure SDPInstance where
  /-- matrix size -/
  k : ℕ
  /-- number of variables -/
  m : ℕ
  /-- `A 0` is the constant term, `A (i+1)` the coefficient of `xᵢ` -/
  A : Fin (m + 1) → Matrix (Fin k) (Fin k) ℚ

namespace SDPInstance

/-- All input matrices are symmetric. -/
def Symmetric (I : SDPInstance) : Prop := ∀ i, (I.A i).IsSymm

/-- `I` is feasible: some real `x ∈ ℝ^m` makes `A₀ + Σᵢ xᵢ Aᵢ₊₁` positive semidefinite. -/
def Feasible (I : SDPInstance) : Prop :=
  ∃ x : Fin I.m → ℝ, (pencil (I.A 0) (fun i => I.A i.succ) x).PosSemidef

/-- Self-delimiting binary code of a natural number. -/
def encNat (n : ℕ) : List Bool := (n.bits.map fun b => [true, b]).flatten ++ [false]

/-- Code of an integer: sign bit, then the absolute value. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- Code of a rational: reduced numerator and denominator. -/
def encRat (q : ℚ) : List Bool := encInt q.num ++ encNat q.den

/-- Bit-string encoding of an instance: `k`, `m`, then the entries of `A 0, …, A m`
row by row. -/
def encode (I : SDPInstance) : List Bool :=
  encNat I.k ++ encNat I.m ++
    (List.ofFn fun i => (List.ofFn fun r => (List.ofFn fun s => encRat (I.A i r s)).flatten
      ).flatten).flatten

end SDPInstance

/-- The SDP feasibility language: encodings of symmetric, feasible instances. -/
def SDPFeasibilityLang : Set (List Bool) :=
  {w | ∃ I : SDPInstance, I.Symmetric ∧ I.encode = w ∧ I.Feasible}

/-- **Polynomial-time decidability of SDP feasibility** (OPEN; ProofAtlas #223,
"Polynomial-Time Decidability of Semidefinite Programming Feasibility"). Exact statement:
*"Determine whether feasibility of a semidefinite program with rational symmetric input
matrices can be decided in polynomial time in the Turing bit model."*

Formalized as: the language `SDPFeasibilityLang` is in `P` (`OneWay.InP`, deterministic
polynomial-time Mathlib `TM2` machines on bit strings). The open problem is to prove or refute
this `Prop`; it is NOT proved here, in either direction.

Modelling simplifications: concrete self-delimiting dense binary encoding
`SDPInstance.encode` (polynomially equivalent to other standard encodings; its injectivity is
not formalized); strings that are not encodings of symmetric instances are outside the
language; feasibility means existence of a *real* solution of the linear matrix inequality
`A₀ + Σ xᵢ Aᵢ ⪰ 0`. See `khachiyan_lower_bound` for the known obstruction to the naive
approach of writing down a feasible point. -/
def SDPFeasibilityInP : Prop := OneWay.InP SDPFeasibilityLang

/-! ## The Khachiyan instance: feasible points of doubly exponential size -/

/-- Constant blocks of the Khachiyan instance: block `0` is `[[0, 2], [2, 2]]`, block
`j ≥ 1` is `[[0, 0], [0, 1]]`. -/
def khB₀ (n : ℕ) (j : Fin (n + 1)) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, if (j : ℕ) = 0 then 2 else 0; if (j : ℕ) = 0 then 2 else 0,
    if (j : ℕ) = 0 then 2 else 1]

/-- Coefficient blocks of `xᵢ`: `xᵢ` sits in the top-left corner of block `i` and in the
off-diagonal positions of block `i + 1`. -/
def khB (n : ℕ) (i j : Fin (n + 1)) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![if i = j then 1 else 0, if (j : ℕ) = i + 1 then 1 else 0;
    if (j : ℕ) = i + 1 then 1 else 0, 0]

/-- The Khachiyan instance before reindexing: block-diagonal matrices indexed by
`Fin 2 × Fin (n + 1)`, whose `j`-th diagonal block of the pencil is
`[[x₀, 2], [2, 2]]` for `j = 0` and `[[x_j, x_{j-1}], [x_{j-1}, 1]]` for `j ≥ 1`. -/
def khA (n : ℕ) (i : Fin (n + 2)) : Matrix (Fin 2 × Fin (n + 1)) (Fin 2 × Fin (n + 1)) ℚ :=
  Fin.cases (blockDiagonal (khB₀ n)) (fun i => blockDiagonal (khB n i)) i

/-- The Khachiyan instance as an `SDPInstance`: `n + 1` variables, `2(n + 1) × 2(n + 1)`
matrices, entries in `{0, 1, 2}`. -/
def khachiyan (n : ℕ) : SDPInstance where
  k := 2 * (n + 1)
  m := n + 1
  A i := (khA n i).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

lemma sum_pred (n : ℕ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    ∑ i : Fin (n + 1), x i * (if (j : ℕ) = i + 1 then (1 : ℝ) else 0) =
      if h : (j : ℕ) = 0 then 0 else x ⟨j - 1, by omega⟩ := by
  split_ifs with h
  · exact Finset.sum_eq_zero fun i _ => by simp; omega
  · rw [Finset.sum_eq_single ⟨j - 1, by omega⟩]
    · simp; omega
    · intro b _ hb
      have : (j : ℕ) ≠ b + 1 := fun h' => hb (Fin.ext (by simp; omega))
      simp [this]
    · simp

lemma khachiyan_block (n : ℕ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    pencil (khB₀ n j) (fun i => khB n i j) x =
      if _h : (j : ℕ) = 0 then !![x j, 2; 2, 2] else !![x j, x ⟨j - 1, by omega⟩;
        x ⟨j - 1, by omega⟩, 1] := by
  have hs := sum_pred n x j
  have hd : ∑ i : Fin (n + 1), x i * (if i = j then (1 : ℝ) else 0) = x j := by simp
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp only [pencil_apply, khB₀, khB] <;> split_ifs at hs ⊢ with h <;>
    simp_all [apply_ite (Rat.cast (K := ℝ))]

lemma khachiyan_pencil (n : ℕ) (x : Fin (n + 1) → ℝ) :
    pencil ((khachiyan n).A 0) (fun i => (khachiyan n).A i.succ) x =
      (blockDiagonal fun j => pencil (khB₀ n j) (fun i => khB n i j) x).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  rw [← pencil_blockDiagonal]
  exact pencil_submatrix (khA n 0) (fun i => khA n i.succ) x _

/-- `x` is feasible for the Khachiyan instance iff all its `2 × 2` blocks are PSD. -/
lemma khachiyan_feasible_iff (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (pencil ((khachiyan n).A 0) (fun i => (khachiyan n).A i.succ) x).PosSemidef ↔
      2 ≤ x 0 ∧ ∀ p : ℕ, ∀ hp : p + 1 < n + 1,
        0 ≤ x ⟨p + 1, hp⟩ ∧ x ⟨p, by omega⟩ ^ 2 ≤ x ⟨p + 1, hp⟩ := by
  rw [khachiyan_pencil]
  refine Iff.trans (posSemidef_submatrix_equiv (M := blockDiagonal _) finProdFinEquiv.symm) ?_
  constructor
  · intro h
    have hb : ∀ j, (pencil (khB₀ n j) (fun i => khB n i j) x).PosSemidef := fun j => by
      have := h.submatrix (fun r : Fin 2 => (r, j))
      convert this using 1
      ext r s; simp [blockDiagonal_apply]
    refine ⟨?_, fun p hp => ?_⟩
    · have := hb 0
      have hj : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
      simp only [khachiyan_block, hj, ↓reduceDIte] at this
      rw [posSemidef_two_iff] at this
      nlinarith [this.1, this.2.2]
    · have := hb ⟨p + 1, hp⟩
      have hj : ((⟨p + 1, hp⟩ : Fin (n + 1)) : ℕ) ≠ 0 := by simp
      simp only [khachiyan_block, hj, ↓reduceDIte] at this
      rw [posSemidef_two_iff] at this
      refine ⟨this.1, ?_⟩
      have h2 := this.2.2
      rw [mul_one] at h2
      convert h2 using 3
      exact Fin.ext (by simp)
  · rintro ⟨h0, hstep⟩
    refine posSemidef_blockDiagonal _ fun j => ?_
    rw [khachiyan_block]
    split_ifs with hj
    · have : j = 0 := Fin.ext hj
      subst this
      rw [posSemidef_two_iff]; refine ⟨by linarith, by norm_num, by nlinarith⟩
    · obtain ⟨_ | p, hp⟩ := j
      · simp at hj
      · obtain ⟨h1, h2⟩ := hstep p hp
        rw [posSemidef_two_iff]
        refine ⟨h1, by norm_num, ?_⟩
        simpa using h2

/-- Known result (Khachiyan's example; see Ramana, *An exact duality theory for semidefinite
programming and its complexity implications*, Math. Prog. 77 (1997), and Porkolab–Khachiyan,
*On the complexity of semidefinite programs*, J. Global Optim. 10 (1997)): every feasible point
of the Khachiyan instance satisfies `x_j ≥ 2^(2^j)` for every `j`, although the instance only
has entries in `{0, 1, 2}`. -/
theorem khachiyan_lower_bound (n : ℕ) (x : Fin (n + 1) → ℝ)
    (hx : (pencil ((khachiyan n).A 0) (fun i => (khachiyan n).A i.succ) x).PosSemidef)
    (j : Fin (n + 1)) : (2 : ℝ) ^ (2 ^ (j : ℕ)) ≤ x j := by
  obtain ⟨h0, hstep⟩ := (khachiyan_feasible_iff n x).1 hx
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero => simpa using h0
  | succ p ih =>
    have ih := ih (by omega)
    obtain ⟨_, h2⟩ := hstep p hj
    have hpos : (0 : ℝ) ≤ 2 ^ 2 ^ p := by positivity
    calc (2 : ℝ) ^ 2 ^ (p + 1) = (2 ^ 2 ^ p) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ x ⟨p, _⟩ ^ 2 := by gcongr
      _ ≤ _ := h2

lemma khA_symm (n : ℕ) (i : Fin (n + 2)) : (khA n i).IsSymm := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [khA, Fin.cases_zero]
    refine IsSymm.ext fun ⟨r, j⟩ ⟨s, j'⟩ => ?_
    simp only [blockDiagonal_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> simp_all [khB₀]
    fin_cases r <;> fin_cases s <;> simp
  · simp only [khA, Fin.cases_succ]
    refine IsSymm.ext fun ⟨r, j⟩ ⟨s, j'⟩ => ?_
    simp only [blockDiagonal_apply]
    split_ifs with h1 h2 h2 <;> subst_vars <;> simp_all [khB]
    fin_cases r <;> fin_cases s <;> simp

/-- Known result (same references): the Khachiyan instance is symmetric and feasible; the
point `x_j = 2^(2^j)` is feasible. -/
theorem khachiyan_feasible (n : ℕ) :
    (khachiyan n).Symmetric ∧ (khachiyan n).Feasible := by
  refine ⟨fun i => (khA_symm n i).submatrix _, ⟨fun j => (2 : ℝ) ^ (2 ^ (j : ℕ)), ?_⟩⟩
  refine (khachiyan_feasible_iff n _).2 ⟨by simp, fun p hp => ⟨by positivity, ?_⟩⟩
  simp only
  rw [← pow_mul, ← pow_succ]

/-- Known consequence (same references): every *rational* feasible point of the Khachiyan
instance has a last coordinate whose numerator is at least `2^(2^n)` in absolute value, so it
needs at least `2^n` bits to write down, while the instance itself has polynomial size. -/
theorem khachiyan_num_lower_bound (n : ℕ) (q : Fin (n + 1) → ℚ)
    (hq : (pencil ((khachiyan n).A 0) (fun i => (khachiyan n).A i.succ)
      (fun i => (q i : ℝ))).PosSemidef) :
    2 ^ (2 ^ n) ≤ (q (Fin.last n)).num.natAbs := by
  have h := khachiyan_lower_bound n _ hq (Fin.last n)
  simp only [Fin.val_last] at h
  have hq' : (2 : ℚ) ^ 2 ^ n ≤ q (Fin.last n) := by exact_mod_cast h
  set r := q (Fin.last n)
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hq'
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.2 hr
  have hden : (1 : ℚ) ≤ r.den := by exact_mod_cast r.den_pos
  have : (r : ℚ) ≤ r.num := by
    rw [← Rat.num_div_den r]
    rw [div_le_iff₀ (by positivity)]
    simp only [Rat.num_div_den]
    have : (0 : ℚ) < r.num := by exact_mod_cast hnum
    nlinarith
  have h2 : ((2 : ℤ) ^ 2 ^ n : ℚ) ≤ (r.num : ℚ) := by push_cast; linarith
  have h3 : (2 : ℤ) ^ 2 ^ n ≤ r.num := by exact_mod_cast h2
  have h4 : ((2 ^ 2 ^ n : ℕ) : ℤ) ≤ (r.num.natAbs : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_pos hnum]; push_cast; exact h3
  exact_mod_cast h4

end CryptoLean.OpenProblems.SDP

#print axioms CryptoLean.OpenProblems.SDP.posSemidef_two_iff
#print axioms CryptoLean.OpenProblems.SDP.posSemidef_blockDiagonal
#print axioms CryptoLean.OpenProblems.SDP.khachiyan_lower_bound
#print axioms CryptoLean.OpenProblems.SDP.khachiyan_feasible
#print axioms CryptoLean.OpenProblems.SDP.khachiyan_num_lower_bound
