import CryptoLean.Combinatorics.BoundedIncidence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation
open CryptoLean.Combinatorics.BoundedIncidence
open Matrix

-- Satisfiable separated-block contracts, with two dependent rows per block.
example :
    let A : Matrix (Fin 4) (Fin 2) ℚ := !![1,0; 1,0; 0,1; 0,1]
    let block : Fin 4 → Fin 2 := ![0,0,1,1]
    let x : Fin 2 → ℚ := ![1,2]
    let s : Fin 2 → ℚ := ![1,2]
    (∀ r c, c ≠ block r → A r c = 0) ∧
      A *ᵥ x = s ∘ block ∧ (∀ i, s i ≠ 0) := by
  dsimp
  constructor
  · intro r c; fin_cases r <;> fin_cases c <;> norm_num
  constructor
  · ext r; fin_cases r <;> norm_num [mulVec, dotProduct, Fin.sum_univ_two]
  · intro i; fin_cases i <;> norm_num

-- Dropping nonzero target values admits a useful-looking isolated zero row.
-- This is a boundary counterexample, not an oracle or DLP claim.
example :
    let A : Matrix (Fin 1) (Fin 1) ℚ := 0
    let y : Fin 1 → ℚ := 1
    y ᵥ* A = 0 ∧ (∑ r, y r * (1 : ℚ)) ≠ 0 := by
  norm_num [vecMul, dotProduct]

-- An incidence degree bound attained by one column covering two targets.
example :
    (({0} : Finset (Fin 1)).biUnion
      (fun _ => ({0,1} : Finset (Fin 3)))).card = 2 := by decide

#print axioms covered_card_le
#print axioms sharing_pairs_card_le
#print axioms block_projection_image
#print axioms separated_block_kernel_tags
