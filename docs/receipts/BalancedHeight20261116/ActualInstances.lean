import CryptoLean.Polynomial.BalancedFiltration
import CryptoLean.Polynomial.ProjectiveQuadratics
import CryptoLean.Semaev.S3
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
noncomputable section

def projectiveWeight : (Fin 4 →₀ ℕ) →+ ℕ :=
  Finsupp.applyAddHom (2 : Fin 4) + Finsupp.applyAddHom (3 : Fin 4)

def liftedS3Row (a b : ℤ) : MvPolynomial (Fin 4) ℤ :=
  let x := MvPolynomial.X (0 : Fin 4)
  let y := MvPolynomial.X (1 : Fin 4)
  let U := MvPolynomial.X (2 : Fin 4)
  let V := MvPolynomial.X (3 : Fin 4)
  (x-y)^2*U^2 - 2*((x+y)*(x*y+MvPolynomial.C a)+2*MvPolynomial.C b)*U*V +
    ((x*y-MvPolynomial.C a)^2-4*MvPolynomial.C b*(x+y))*V^2

example (p t : ℕ) (hp : 0 < p) (a b : ℤ)
    (f : MvPolynomial (Fin 4) ℤ)
    (hf : f ∈ (Ideal.span {MvPolynomial.C (p : ℤ), liftedS3Row a b})^t)
    (m : Fin 4 →₀ ℕ) (hc : f.coeff m ≠ 0) :
    p^(2*t) ≤ (f.coeff m).natAbs^2 * p^(projectiveWeight m) := by
  apply CryptoLean.BalancedFiltration.span_power_coefficient_lower
    p hp projectiveWeight t _ ?_ f hf m hc
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact CryptoLean.BalancedFiltration.modulus_mem p projectiveWeight
  · have h := CryptoLean.BalancedFiltration.quadratic_chart_mem p projectiveWeight
      (2 : Fin 4) (3 : Fin 4) (by simp [projectiveWeight, Finsupp.applyAddHom])
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      ((MvPolynomial.X (0 : Fin 4)-MvPolynomial.X 1)^2)
      (-2*((MvPolynomial.X (0 : Fin 4)+MvPolynomial.X 1)*
        (MvPolynomial.X 0*MvPolynomial.X 1+MvPolynomial.C a)+2*MvPolynomial.C b))
      ((MvPolynomial.X (0 : Fin 4)*MvPolynomial.X 1-MvPolynomial.C a)^2-
        4*MvPolynomial.C b*(MvPolynomial.X 0+MvPolynomial.X 1))
    convert h using 1
    dsimp [liftedS3Row]
    ring

example (p : ℕ) [Fact p.Prime] (a b x y U V : ZMod p) (hV : V ≠ 0) :
    V^2 * CryptoLean.Semaev.S3 a b x y (U/V) =
      (x-y)^2*U^2 - 2*((x+y)*(x*y+a)+2*b)*U*V +
        ((x*y-a)^2-4*b*(x+y))*V^2 := by
  unfold CryptoLean.Semaev.S3
  field_simp

example (t d : ℕ) : 2*t ≤ 2*(t-d/2)+d := by omega

example {σ : Type*} [DecidableEq σ] (p : ℕ) (w : (σ →₀ ℕ) →+ ℕ) :
    (MvPolynomial.C (p : ℤ) : MvPolynomial σ ℤ) ∈
      CryptoLean.BalancedFiltration.filtrationIdeal p w 1 :=
  CryptoLean.BalancedFiltration.modulus_mem p w

example (p : ℕ) [Fact p.Prime] (a b x y z q U V : ZMod p) (hV : V ≠ 0) :
    let A := (x-y)^2
    let B := -2*((x+y)*(x*y+a)+2*b)
    let C := (x*y-a)^2-4*b*(x+y)
    let D := (z-q)^2
    let E := -2*((z+q)*(z*q+a)+2*b)
    let F := (z*q-a)^2-4*b*(z+q)
    A*U^2+B*U*V+C*V^2=0 → D*U^2+E*U*V+F*V^2=0 →
      (A*F-C*D)^2-(A*E-B*D)*(B*F-C*E)=0 := by
  intro A B C D E F hF hG
  exact CryptoLean.ProjectiveQuadratics.common_root A B C D E F U V hV hF hG
