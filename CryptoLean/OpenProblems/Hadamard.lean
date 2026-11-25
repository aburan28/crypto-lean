import Mathlib

namespace CryptoLean.OpenProblems.Hadamard

open Matrix
open scoped Kronecker

/-- Concrete ±1 Hadamard matrix of order `n`: entries in `{1, -1}` and `H * Hᵀ = n • 1`. -/
def IsHadamardMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * Hᵀ = (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ)

/-- A Hadamard matrix of order `n` exists. -/
def HadamardOrder (n : ℕ) : Prop := ∃ H : Matrix (Fin n) (Fin n) ℤ, IsHadamardMatrix H

/-- Bridge: the concrete definition agrees with Mathlib's `Matrix.IsHadamard` over `ℤ`. -/
theorem isHadamardMatrix_iff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) :
    IsHadamardMatrix H ↔ H.IsHadamard := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · constructor
    · intro _
      exact ⟨fun i => i.elim0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · intro _
      exact ⟨fun i => i.elim0, Subsingleton.elim _ _⟩
  · have hreg : IsRegular ((Fintype.card (Fin n) : ℕ) : ℤ) := by
      rw [Fintype.card_fin]
      exact IsRegular.of_ne_zero (by exact_mod_cast hn.ne')
    rw [isHadamard_iff_mul_conjTranspose hreg, conjTranspose_eq_transpose_of_trivial,
      Fintype.card_fin]
    simp only [IsHadamardMatrix, Unitary.mem_iff_eq_one_or_eq_neg_one]


/-- Existence of a Hadamard matrix of order `n`, phrased with Mathlib's `Matrix.IsHadamard`. -/
theorem hadamardOrder_iff (n : ℕ) :
    HadamardOrder n ↔ ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard := by
  simp only [HadamardOrder, isHadamardMatrix_iff]

/-- A Hadamard matrix indexed by any finite type `ι` yields one of order `card ι`. -/
theorem hadamardOrder_of_fintype {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℤ} (hH : H.IsHadamard) : HadamardOrder (Fintype.card ι) := by
  rw [hadamardOrder_iff]
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  exact ⟨reindex e e H, hH.reindex e e⟩

/-- **Kronecker (Sylvester) product construction** (known result; Sylvester 1867,
see de Launey–Flannery, *Algebraic Design Theory*, §2.3): if Hadamard matrices of orders
`m` and `n` exist, then a Hadamard matrix of order `m * n` exists. -/
theorem hadamardOrder_mul {m n : ℕ} (hm : HadamardOrder m) (hn : HadamardOrder n) :
    HadamardOrder (m * n) := by
  rw [hadamardOrder_iff] at hm hn
  obtain ⟨A, hA⟩ := hm
  obtain ⟨B, hB⟩ := hn
  have := hadamardOrder_of_fintype (hA.kronecker hB)
  simpa [Fintype.card_prod, Fintype.card_fin] using this

/-- The `1 × 1` matrix `(1)` is Hadamard. -/
theorem hadamardOrder_one : HadamardOrder 1 :=
  ⟨1, fun i j => by fin_cases i; fin_cases j; simp, by decide⟩

/-- The `2 × 2` Sylvester matrix `!![1, 1; 1, -1]` is Hadamard. -/
theorem hadamardOrder_two : HadamardOrder 2 :=
  ⟨!![1, 1; 1, -1], fun i j => by fin_cases i <;> fin_cases j <;> simp, by decide⟩

/-- **Sylvester's theorem** (known result; J. J. Sylvester, *Thoughts on inverse orthogonal
matrices…*, Phil. Mag. 1867): a Hadamard matrix of order `2 ^ k` exists for every `k`. -/
theorem hadamardOrder_two_pow (k : ℕ) : HadamardOrder (2 ^ k) := by
  induction k with
  | zero => simpa using hadamardOrder_one
  | succ k ih => rw [pow_succ]; exact hadamardOrder_mul ih hadamardOrder_two

/-- **Classical necessary condition** (known result; Paley 1933, see also Hedayat–Wallis,
*Hadamard matrices and their applications*, Ann. Statist. 1978, Thm 1.1): if a Hadamard
matrix of order `n` exists then `n = 1`, `n = 2`, or `4 ∣ n`.
(The empty matrix of order `0` is included in the last case, since `4 ∣ 0`.) -/
theorem hadamardOrder_necessary {n : ℕ} (h : HadamardOrder n) :
    n = 1 ∨ n = 2 ∨ 4 ∣ n := by
  rw [hadamardOrder_iff] at h
  obtain ⟨H, hH⟩ := h
  by_cases hn : 2 < n
  · right; right
    simpa using hH.four_dvd_card (by simpa using hn)
  · interval_cases n <;> simp

/-- Consequence of the necessary condition: there is no Hadamard matrix of order `n`
for `n > 2` with `n ≢ 0 (mod 4)` (e.g. orders 3, 5, 6, 7, 10). Known result (as above). -/
theorem not_hadamardOrder_of_not_dvd {n : ℕ} (hn : 2 < n) (h4 : ¬ 4 ∣ n) :
    ¬ HadamardOrder n := by
  intro h
  rcases hadamardOrder_necessary h with h1 | h2 | h3
  · omega
  · omega
  · exact h4 h3

/-- **The Hadamard conjecture** (OPEN; ProofAtlas #20, "Hadamard Matrix Existence
Conjecture"): *for every positive integer `k` there exists a Hadamard matrix of order `4k`*,
i.e. an `4k × 4k` matrix with entries `±1` whose rows are mutually orthogonal
(`H Hᵀ = 4k·I`). (Quoted in the standard form; the ProofAtlas entry text was not available
offline when this file was written.)

Modelling note: matrices are `Matrix (Fin (4*k)) (Fin (4*k)) ℤ` with entries in `{1,-1}` and
`H * Hᵀ = (4k) • 1`; by `isHadamardMatrix_iff` this coincides with Mathlib's
`Matrix.IsHadamard` over `ℤ`. This is stated as a `Prop` only; it is NOT proved here.
The smallest open order is currently `668`. -/
def HadamardConjecture : Prop := ∀ k : ℕ, 1 ≤ k → HadamardOrder (4 * k)

/-- **Partial result** (known result; immediate from Sylvester 1867): the Hadamard conjecture
holds for every `k` that is a power of two, since `4 * 2^j = 2^(j+2)`. -/
theorem hadamardConjecture_of_pow_two (j : ℕ) : HadamardOrder (4 * 2 ^ j) := by
  have : 4 * 2 ^ j = 2 ^ (j + 2) := by rw [pow_add]; ring
  rw [this]
  exact hadamardOrder_two_pow _

/-- Known result (closure of the set of Hadamard orders under products, Sylvester 1867):
if the conjecture's instances hold for `k₁` and `k₂`, then a Hadamard matrix of order
`4 * (4 * k₁ * k₂)` exists, i.e. the instance `k = 4 k₁ k₂` holds. -/
theorem hadamardConjecture_instance_mul {k₁ k₂ : ℕ} (h₁ : HadamardOrder (4 * k₁))
    (h₂ : HadamardOrder (4 * k₂)) : HadamardOrder (4 * (4 * k₁ * k₂)) := by
  have := hadamardOrder_mul h₁ h₂
  convert this using 1
  ring

/-- Known result: the instance of the conjecture for `k` lifts to `2k` (doubling via the
`2 × 2` Sylvester matrix). -/
theorem hadamardOrder_four_mul_two_mul {k : ℕ} (h : HadamardOrder (4 * k)) :
    HadamardOrder (4 * (2 * k)) := by
  have := hadamardOrder_mul h hadamardOrder_two
  convert this using 1
  ring

/-- Quadratic character modulo `11`, with the value at `0` set to `1` (this places the
identity on the diagonal of the Paley type I matrix below). Residues mod 11: `{1,3,4,5,9}`. -/
def chi11 (a : ℕ) : ℤ := if a % 11 ∈ [0, 1, 3, 4, 5, 9] then 1 else -1

/-- The Paley type I matrix of order `q + 1 = 12` for `q = 11`: `H = I + S` with
`S = [[0, 1ᵀ], [-1, Q]]`, `Q i j = χ(j - i)`. -/
def paley12 : Matrix (Fin 12) (Fin 12) ℤ := fun i j =>
  if i.val = 0 then 1 else if j.val = 0 then -1 else chi11 (j.val + 11 - i.val)

/-- **Order 12** (known result; Paley, *On orthogonal matrices*, J. Math. Phys. 1933,
type I construction with `q = 11`): `paley12` is a Hadamard matrix, so the conjecture's
instance `k = 3` (not a power of two) holds. Checked by kernel `decide`. -/
theorem isHadamardMatrix_paley12 : IsHadamardMatrix paley12 := by
  refine ⟨?_, by decide⟩
  intro i j
  revert i j
  unfold paley12
  decide

/-- Known result (Paley 1933): a Hadamard matrix of order `12 = 4 * 3` exists. -/
theorem hadamardOrder_twelve : HadamardOrder (4 * 3) := ⟨paley12, isHadamardMatrix_paley12⟩

end CryptoLean.OpenProblems.Hadamard

#print axioms CryptoLean.OpenProblems.Hadamard.isHadamardMatrix_iff
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardOrder_mul
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardOrder_two_pow
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardOrder_necessary
#print axioms CryptoLean.OpenProblems.Hadamard.not_hadamardOrder_of_not_dvd
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardConjecture_of_pow_two
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardConjecture_instance_mul
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardOrder_four_mul_two_mul
#print axioms CryptoLean.OpenProblems.Hadamard.isHadamardMatrix_paley12
#print axioms CryptoLean.OpenProblems.Hadamard.hadamardOrder_twelve
