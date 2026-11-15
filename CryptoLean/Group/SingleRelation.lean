import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.LinearCombination

/-! Semantic label and index identities for a single-relation reduction.
No statement below constructs a relation selector or proves its cost/yield. -/
set_option autoImplicit false
namespace CryptoLean.SingleRelation

/-- For fixed mixed values, the second labels are completely free. This is
a semantic equivalence; the hidden scalar `k` is used in a proof, not supplied
to a discrete-log algorithm. -/
def mixedLabelFiberEquiv {R I : Type*} [CommRing R] (k : R) (u : I → R) :
    (I → R) ≃ {ab : (I → R) × (I → R) // ∀ i, ab.1 i + k * ab.2 i = u i} where
  toFun b := ⟨((fun i => u i - k * b i), b), fun i => by ring⟩
  invFun ab := ab.val.2
  left_inv _ := rfl
  right_inv ab := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have h := ab.property i
      dsimp
      linear_combination -h
    · rfl

/-- Exact cardinality of the full label fibre, with all second-label vectors
represented once. Conditional probability statements require their separate
uniform-sampling and label-free-selection hypotheses. -/
theorem mixed_label_fiber_card {R I : Type*} [CommRing R] [Finite I]
    (k : R) (u : I → R) :
    Nat.card {ab : (I → R) × (I → R) // ∀ i, ab.1 i + k * ab.2 i = u i} =
      Nat.card R ^ Nat.card I := by
  rw [← Nat.card_congr (mixedLabelFiberEquiv k u), Nat.card_fun]

/-- A checked weighted zero-sum relation recovers the scalar when the
coefficient of the unknown point is nonzero. -/
theorem recover_from_relation {K I : Type*} [Field K]
    (s : Finset I) (a b c : I → K) (k : K)
    (h : ∑ i ∈ s, c i * (a i + k * b i) = 0)
    (hb : (∑ i ∈ s, c i * b i) ≠ 0) :
    -(∑ i ∈ s, c i * a i) / (∑ i ∈ s, c i * b i) = k := by
  have hsum : (∑ i ∈ s, c i * a i) + k * (∑ i ∈ s, c i * b i) = 0 := by
    simpa [Finset.sum_add_distrib, Finset.mul_sum, mul_add, mul_assoc, mul_left_comm] using h
  apply (div_eq_iff hb).mpr
  linear_combination -hsum

/-- The complete degree-b monomial universe in m variables has at least
b^m/m! columns. It is an arithmetic inequality, not a lower bound for all
polynomial-system algorithms. -/
theorem direct_index_size (b m : ℕ) :
    b^m ≤ m.factorial * (b+m).choose m := by
  calc
    b^m ≤ (b+1)^m := Nat.pow_le_pow_left (Nat.le_succ b) m
    _ ≤ (b+1).ascFactorial m := Nat.pow_succ_le_ascFactorial (b+1) m
    _ = m.factorial * (b+m).choose m := Nat.ascFactorial_eq_factorial_mul_choose b m

end CryptoLean.SingleRelation
