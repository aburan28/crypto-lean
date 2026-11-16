import CryptoLean.Polynomial.CubicAdicLifting

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial CryptoLean.CubicAdicLifting CryptoLean.NormSaturatedInterpolation

namespace CubicAdicActual
variable {K : Type*} [Field K]

theorem horizontal_tight_row_lost_by_capped_root [DecidableEq K] (r s : K)
    (hx : Function.Injective (fun i : Fin 3 ↦ ![r,s,-(r+s)] i)) :
    let a := -(r^2+r*s+s^2)
    let b := 1+r*s*(r+s)
    let x : Fin 3 → K := ![r,s,-(r+s)]
    (∀ i, (-1:K)^2=(x i)^3+a*x i+b ∧
      (1:K[X]).eval (x i)+(-1)*(1:K[X]).eval (x i)=0) ∧
    (curveNorm a b 1 1).natDegree=3 ∧
    (∀ z w : K, w^2=z^3+a*z+b →
      ((1:K[X]).eval z+w*(1:K[X]).eval z=0 ↔ ∃ i, z=x i ∧ w= -1)) ∧
    ¬ ∃ U : K[X], U.natDegree ≤ 2 ∧ (curveCubic a b)^2 ∣ U^2-(curveNorm a b 1 1) := by
  dsimp
  let a := -(r^2+r*s+s^2)
  let b := 1+r*s*(r+s)
  let x : Fin 3 → K := ![r,s,-(r+s)]
  have hrec := horizontal_curve_records r s
  have hd : (curveNorm a b 1 1).natDegree=3 := by
    simp only [curveNorm,one_pow,mul_one]
    exact one_sub_cubic_degree a b
  refine ⟨hrec,hd,?_,?_⟩
  · intro z w hw
    have h := tight_curve_zero_locus (Finset.univ : Finset (Fin 3)) x (fun _ ↦ (-1:K)) hx.injOn
      a b 1 1 (by simp) (fun i _ ↦ (hrec i).1) (fun i _ ↦ (hrec i).2)
      (by simpa only [hd,Finset.card_univ,Fintype.card_fin] using (le_refl 3)) z w hw
    simpa [x] using h
  · rw [(full_norm_without_capped_root a b).1]
    exact capped_lift_rejects_full_norm a b

theorem retained_norm_precision_keeps_horizontal_row (r s : K) :
    let a := -(r^2+r*s+s^2)
    let b := 1+r*s*(r+s)
    ((curveCubic a b)^2 ∣ curveNorm a b 1 1-(1-curveCubic a b)) ↔
      curveNorm a b 1 1=1-curveCubic a b := by
  dsimp
  apply bounded_full_norm_precision_iff (k:=2) (t:=3)
  · simp
  · simp
  · simp only [one_sub_cubic_degree,le_refl]
  · decide

theorem explicit_lift_degree_jump (a b : K) (htwo : (2:K) ≠ 0) :
    let U : K[X] := 1-C ((2:K)⁻¹)*curveCubic a b
    U.natDegree=3 ∧ (curveCubic a b)^2 ∣ U^2-(1-curveCubic a b) := by
  dsimp
  have ht : (2:K[X])*C ((2:K)⁻¹)=1 := by
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (C : K →+* K[X]) (mul_inv_cancel₀ htwo)
  have hc : (C ((2:K)⁻¹) : K[X]) ≠ 0 := by simp [htwo]
  have hd : (C ((2:K)⁻¹)*curveCubic a b).natDegree=3 := by
    rw [Polynomial.natDegree_mul hc (curveCubic_ne_zero a b),Polynomial.natDegree_C,
      curveCubic_natDegree,zero_add]
  constructor
  · exact (Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp [hd])).trans hd
  · refine ⟨(C ((2:K)⁻¹))^2,?_⟩
    linear_combination -(curveCubic a b)*ht

end CubicAdicActual
