import CryptoLean.SplitPrime.GL4Core

namespace CryptoLean.SLP
universe u
variable {F : Type u} [Field F] {n m : ℕ}

-- NAME CHECK: `Matrix.mulVec` unfolding, root-level `dotProduct`, `Fin.sum_univ_def`.
theorem rowApply_eq_mulVec (A : Matrix (Fin m) (Fin n) F) (w : Fin n → F) :
    rowApply A w = A.mulVec w := by
  funext i
  simp only [rowApply, Matrix.mulVec, dotProduct]
  exact (Fin.sum_univ_def _).symm

-- NAME CHECK: `Matrix.mulVec_mulVec`, `Units.inv_mul`, `Matrix.one_mulVec`.
theorem rowApply_inv_cancel (g : Matrix.GeneralLinearGroup (Fin n) F) (x : Fin n → F) :
    rowApply (g⁻¹).val (rowApply g.val x) = x := by
  rw [rowApply_eq_mulVec, rowApply_eq_mulVec, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec]

/-- **Lemma 2 (one step).** Coordinates `w = g V`: the program for
`w ↦ h · P(g⁻¹ · w)` has the same M and S counts. Memo case: `h = g`, `n = m = 4`. -/
theorem reparam_GL (g : Matrix.GeneralLinearGroup (Fin n) F)
    (h : Matrix.GeneralLinearGroup (Fin m) F) (P : Prog F n m) :
    (P.reparam (g⁻¹).val h.val).mulCount = P.mulCount ∧
    (P.reparam (g⁻¹).val h.val).sqCount = P.sqCount ∧
    ∀ w, (P.reparam (g⁻¹).val h.val).eval w
        = h.val.mulVec (P.eval ((g⁻¹).val.mulVec w)) := by
  refine ⟨Prog.mulCount_reparam _ _ _, Prog.sqCount_reparam _ _ _, fun w => ?_⟩
  rw [Prog.eval_reparam, rowApply_eq_mulVec, rowApply_eq_mulVec]

/-- **Lemma 2 (invariance).** The set of achievable (M, S) profiles is the same
for `f` and for `w ↦ h · f(g⁻¹ · w)`. -/
theorem GL_invariance (g : Matrix.GeneralLinearGroup (Fin n) F)
    (h : Matrix.GeneralLinearGroup (Fin m) F)
    (f : (Fin n → F) → (Fin m → F)) (a s : ℕ) :
    (∃ P : Prog F n m, (∀ x, P.eval x = f x) ∧ P.mulCount = a ∧ P.sqCount = s) ↔
    (∃ Q : Prog F n m, (∀ w, Q.eval w = h.val.mulVec (f ((g⁻¹).val.mulVec w))) ∧
        Q.mulCount = a ∧ Q.sqCount = s) := by
  have key := exists_prog_iff (g⁻¹).val g.val h.val (h⁻¹).val
    (rowApply_inv_cancel g) (rowApply_inv_cancel h) f a s
  simpa only [rowApply_eq_mulVec] using key

/-- Exception locus: the new output vanishes iff the old one does. -/
-- NAME CHECK: `Matrix.mulVec_zero`.
theorem GL_mulVec_eq_zero_iff (h : Matrix.GeneralLinearGroup (Fin m) F)
    (y : Fin m → F) : h.val.mulVec y = 0 ↔ y = 0 := by
  constructor
  · intro hy
    calc y = (h⁻¹).val.mulVec (h.val.mulVec y) := by
            rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      _ = 0 := by rw [hy, Matrix.mulVec_zero]
  · rintro rfl
    exact Matrix.mulVec_zero _

end CryptoLean.SLP
