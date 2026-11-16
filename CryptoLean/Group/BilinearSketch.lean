import CryptoLean.Group.ShortlistCompletion
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Tactic

/-! Raw finite-mask success for a nonzero bilinear parity sketch. The
input matrix is arbitrary; no input-point or output-uniformity law is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.BilinearSketch

theorem surjective_of_value_one {R : Type*} [AddGroup R]
    (f : R →+ ZMod 2) (r : R) (hr : f r = 1) : Function.Surjective f := by
  intro z
  fin_cases z
  · exact ⟨0, map_zero f⟩
  · exact ⟨r, hr⟩

/-- Any predicate containing a nonzero binary functional's one-fiber
contains at least half the raw mask space. -/
theorem half_count {C : Type*} [AddGroup C] [Fintype C] (f : C →+ ZMod 2)
    (c0 : C) (hc0 : f c0 = 1) (S : C → Prop) (hS : ∀ c, f c = 1 → S c) :
    Nat.card C ≤ 2 * Nat.card {c : C // S c} := by
  classical
  have hf : Nat.card {c : C // f c = 1} * 2 = Nat.card C := by
    simpa [Nat.card_eq_fintype_card] using
      ShortlistCompletion.fiber_card_mul f (surjective_of_value_one f c0 hc0) 1
  let embed : {c : C // f c = 1} → {c : C // S c} := fun c ↦ ⟨c.val, hS c.val c.property⟩
  have hinj : Function.Injective embed := by
    intro c d h
    exact Subtype.ext (congrArg (fun w : {c : C // S c} ↦ w.val) h)
  have hc : Nat.card {c : C // f c = 1} ≤ Nat.card {c : C // S c} := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective embed hinj
  calc
    Nat.card C = Nat.card {c : C // f c = 1} * 2 := hf.symm
    _ ≤ Nat.card {c : C // S c} * 2 := Nat.mul_le_mul_right 2 hc
    _ = 2 * Nat.card {c : C // S c} := Nat.mul_comm _ _

theorem quarter_count {R C : Type*} [AddGroup R] [AddGroup C]
    [Fintype R] [Fintype C] (B : R →+ C →+ ZMod 2)
    (r0 : R) (c0 : C) (hentry : B r0 c0 = 1) :
    Nat.card R * Nat.card C ≤ 4 * Nat.card {w : R × C // B w.1 w.2 = 1} := by
  classical
  let Rows := {r : R // B r c0 = 1}
  let Witness := Σ r : Rows, {c : C // B r.val c = 1}
  let Success := {w : R × C // B w.1 w.2 = 1}
  have hrow : Nat.card Rows * 2 = Nat.card R := by
    simpa [Rows, Nat.card_eq_fintype_card] using
      ShortlistCompletion.fiber_card_mul (B.flip c0)
        (surjective_of_value_one (B.flip c0) r0 hentry) 1
  have hfiber (r : Rows) : Fintype.card {c : C // B r.val c = 1} * 2 = Fintype.card C := by
    simpa [Nat.card_eq_fintype_card] using
      ShortlistCompletion.fiber_card_mul (B r.val)
        (surjective_of_value_one (B r.val) c0 r.property) 1
  have hwitness : Nat.card Witness * 2 = Nat.card Rows * Nat.card C := by
    simp only [Witness, Nat.card_eq_fintype_card, Fintype.card_sigma, Finset.sum_mul]
    simp_rw [hfiber]
    simp
  let embed : Witness → Success := fun w ↦ ⟨(w.1.val, w.2.val), w.2.property⟩
  have hinj : Function.Injective embed := by
    rintro ⟨r, c⟩ ⟨r', c'⟩ h
    have hr : r = r' := Subtype.ext (congrArg (fun w : Success ↦ w.val.1) h)
    subst r'
    have hc : c = c' := Subtype.ext (congrArg (fun w : Success ↦ w.val.2) h)
    cases hc
    rfl
  have hcard : Nat.card Witness ≤ Nat.card Success := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective embed hinj
  calc
    Nat.card R * Nat.card C = (Nat.card Rows * 2) * Nat.card C := by rw [hrow]
    _ = (Nat.card Rows * Nat.card C) * 2 := by ring
    _ = (Nat.card Witness * 2) * 2 := by rw [hwitness]
    _ = 4 * Nat.card Witness := by ring
    _ ≤ 4 * Nat.card Success := Nat.mul_le_mul_left 4 hcard

def matrixSketch {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (M : Matrix I J (ZMod 2)) : (I → ZMod 2) →+ (J → ZMod 2) →+ ZMod 2 :=
  (LinearMap.toAddMonoidHom' :
    ((J → ZMod 2) →ₗ[ZMod 2] ZMod 2) →+ ((J → ZMod 2) →+ ZMod 2)).comp
      (Matrix.toLinearMap₂' (S₁ := ZMod 2) (S₂ := ZMod 2) (ZMod 2) M).toAddMonoidHom

theorem matrixSketch_single {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J (ZMod 2)) (i : I) (j : J) :
    matrixSketch M (Pi.single i 1) (Pi.single j 1) = M i j := by
  change Matrix.toLinearMap₂' (S₁ := ZMod 2) (S₂ := ZMod 2) (ZMod 2) M
    (Pi.single i (1 : ZMod 2)) (Pi.single j (1 : ZMod 2)) = M i j
  rw [Matrix.toLinearMap₂'_apply']
  simp

theorem matrixSketch_row {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J (ZMod 2)) (i : I) (c : J → ZMod 2) :
    matrixSketch M (Pi.single i 1) c = (M.mulVec c) i := by
  change Matrix.toLinearMap₂' (S₁ := ZMod 2) (S₂ := ZMod 2) (ZMod 2) M
    (Pi.single i (1 : ZMod 2)) c = (M.mulVec c) i
  rw [Matrix.toLinearMap₂'_apply']
  simp

theorem matrix_half_count {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J (ZMod 2))
    (i : I) (j : J) (hentry : M i j = 1) :
    Nat.card (J → ZMod 2) ≤ 2 * Nat.card {c : J → ZMod 2 // M.mulVec c ≠ 0} := by
  apply half_count (matrixSketch M (Pi.single i 1)) (Pi.single j 1)
    ((matrixSketch_single M i j).trans hentry) (fun c ↦ M.mulVec c ≠ 0)
  intro c hc hz
  rw [matrixSketch_row] at hc
  have hzrow : (M.mulVec c) i = 0 := congrFun hz i
  exact zero_ne_one (hzrow.symm.trans hc)

theorem matrix_quarter_count {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J (ZMod 2))
    (i : I) (j : J) (hentry : M i j = 1) :
    Nat.card (I → ZMod 2) * Nat.card (J → ZMod 2) ≤
      4 * Nat.card {w : (I → ZMod 2) × (J → ZMod 2) // matrixSketch M w.1 w.2 = 1} :=
  quarter_count (matrixSketch M) (Pi.single i 1) (Pi.single j 1)
    ((matrixSketch_single M i j).trans hentry)

end CryptoLean.BilinearSketch
