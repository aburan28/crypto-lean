import CryptoLean.Curve.SubgroupDLog

/-!
# Transporting a discrete logarithm through an isogeny

For an additive map with a dual of degree prime to the subgroup order, composing
the dual with multiplication by the inverse degree recovers each challenge point.
The target base-point order follows from `ConductorGap.addOrderOf_map_eq`.
The correctness statements allow solvers to inspect point coordinates.
-/

set_option autoImplicit false

namespace CryptoLean.ECDLP

section Group

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {r d : ℕ} [Fact r.Prime]

private theorem inverse_degree_smul (P : G) (horder : addOrderOf P = r) (hcoprime : ¬ r ∣ d) :
    ((d : ZMod r)⁻¹).val • (d • P) = P := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have hd : (d : ZMod r) ≠ 0 := mt (ZMod.natCast_eq_zero_iff d r).mp hcoprime
  calc
    ((d : ZMod r)⁻¹).val • (d • P) = (((d : ZMod r)⁻¹).val * d) • P := (mul_smul _ _ _).symm
    _ = scalarToPoint P horder (↑(((d : ZMod r)⁻¹).val * d : ℕ)) :=
      (scalarToPoint_natCast P horder _).symm
    _ = scalarToPoint P horder 1 := by rw [Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hd]
    _ = P := by simpa using scalarToPoint_natCast P horder 1

/-- The adjusted dual returns the challenge for the same scalar at the source base point. -/
theorem adjusted_dual_recovers_challenge (φ : G →+ H) (ψ : H →+ G) (hdual : ∀ R, ψ (φ R) = d • R)
    (P : G) (horder : addOrderOf P = r) (hcoprime : ¬ r ∣ d) (k : ℕ) :
    ((d : ZMod r)⁻¹).val • ψ (k • φ P) = k • P := by
  calc
    ((d : ZMod r)⁻¹).val • ψ (k • φ P) = ((d : ZMod r)⁻¹).val • (k • (d • P)) := by
      rw [map_nsmul, hdual P]
    _ = k • (((d : ZMod r)⁻¹).val • (d • P)) := smul_comm _ _ _
    _ = k • P := by rw [inverse_degree_smul P horder hcoprime]

/-- Success on a uniformly chosen scalar for a solver with access to its input point. -/
noncomputable def solverSuccessProbability (P : G) (solve : G → ZMod r) : ℝ := by
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  exact ((Finset.univ.filter fun x => solve (x.val • P) = x).card : ℝ) / r

/-- A call to the other solver preserves the exact success probability in either direction. -/
theorem solver_reductions_of_dual (φ : G →+ H) (ψ : H →+ G) (hdual : ∀ R, ψ (φ R) = d • R)
    (P : G) (horder : addOrderOf P = r) (hcoprime : ¬ r ∣ d)
    (solve₀ : G → ZMod r) (solve₁ : H → ZMod r) :
    solverSuccessProbability P (solve₁ ∘ φ) = solverSuccessProbability (φ P) solve₁ ∧
      solverSuccessProbability (φ P) (fun Q => solve₀ (((d : ZMod r)⁻¹).val • ψ Q)) =
        solverSuccessProbability P solve₀ := by
  constructor
  · unfold solverSuccessProbability
    simp only [Function.comp_apply, map_nsmul]
  · unfold solverSuccessProbability
    simp only [adjusted_dual_recovers_challenge φ ψ hdual P horder hcoprime]

end Group

end CryptoLean.ECDLP
