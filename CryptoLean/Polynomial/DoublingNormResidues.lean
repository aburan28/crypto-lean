import CryptoLean.Polynomial.MonicNormSelector
import CryptoLean.Curve.CenteredCompletion

/-! Exact tangent-derived square residues modulo the actual short cubic.
The subgroup halving/Mathlib point-coordinate bridge is separate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.DoublingNormResidues
open Polynomial CryptoLean.NormSaturatedInterpolation
variable {R : Type*} [CommRing R]

theorem cleared_tangent_residue (a b r s m z : R)
    (hcurve : s^2=r^3+a*r+b) (hslope : 2*s*m=3*r^2+a) :
    (s*m-(z^2+r*z+r^2+a))^2-s^2*(m^2-2*r-z)=
      (z^3+a*z+b)*(z+2*r) := by
  linear_combination (z+2*r)*hcurve-(z^2+r*z+r^2+a)*hslope

theorem unit_tangent_residue (a b r s m t z : R)
    (hcurve : s^2=r^3+a*r+b) (hslope : 2*s*m=3*r^2+a) (hst : s*t=1) :
    (m-t*(z^2+r*z+r^2+a))^2-(m^2-2*r-z)=
      (z^3+a*z+b)*(z+2*r)*t^2 := by
  let Q := z^2+r*z+r^2+a
  let H := m-t*Q
  have hJ : s*H=s*m-Q := by
    calc
      s*H=s*m-(s*t)*Q := by dsimp [H]; ring
      _ = s*m-Q := by rw [hst,one_mul]
  have hc := cleared_tangent_residue a b r s m z hcurve hslope
  have hmult : s^2*(H^2-(m^2-2*r-z))=(z^3+a*z+b)*(z+2*r) := by
    calc
      s^2*(H^2-(m^2-2*r-z))=(s*H)^2-s^2*(m^2-2*r-z) := by ring
      _ = _ := by rw [hJ]; exact hc
  have hinv : t^2*s^2=1 := by rw [← mul_pow,mul_comm t s,hst,one_pow]
  calc
    H^2-(m^2-2*r-z)=(t^2*s^2)*(H^2-(m^2-2*r-z)) := by rw [hinv,one_mul]
    _ = t^2*(s^2*(H^2-(m^2-2*r-z))) := by ring
    _ = t^2*((z^3+a*z+b)*(z+2*r)) := by rw [hmult]
    _ = (z^3+a*z+b)*(z+2*r)*t^2 := by ring

variable {K : Type*} [Field K]

def doublingResidue (a r s m : K) : K[X] :=
  C m-C s⁻¹*(X^2+C r*X+C (r^2+a))

theorem polynomial_tangent_residue (a b r s m : K) (hs : s ≠ 0)
    (hcurve : s^2=r^3+a*r+b) (hslope : 2*s*m=3*r^2+a) :
    (doublingResidue a r s m)^2-(C (m^2-2*r)-X)=
      curveCubic a b*(X+C (2*r))*C s⁻¹^2 := by
  have hc : (C s : K[X])^2=(C r)^3+C a*C r+C b := by
    simpa only [map_pow,map_add,map_mul] using congrArg (C : K →+* K[X]) hcurve
  have hm : (2:K[X])*C s*C m=3*(C r)^2+C a := by
    simpa only [map_pow,map_add,map_mul,map_ofNat] using congrArg (C : K →+* K[X]) hslope
  have hi : (C s : K[X])*C s⁻¹=1 := by rw [← map_mul,mul_inv_cancel₀ hs,map_one]
  have h := @unit_tangent_residue (Polynomial K) (@Polynomial.commRing K inferInstance)
    (C a) (C b) (C r) (C s) (C m) (C s⁻¹) X hc hm hi
  have hQ : (C (r^2+a) : K[X])=(C r)^2+C a := by rw [map_add,map_pow]
  have hx : (C (m^2-2*r) : K[X])=(C m)^2-2*C r := by
    rw [map_sub,map_pow,map_mul,map_ofNat]
  have hd : (C (2*r) : K[X])=2*C r := by rw [map_mul,map_ofNat]
  unfold doublingResidue curveCubic
  rw [hQ,hx,hd]
  simpa only [add_assoc] using h

theorem doubled_abscissa_square_residue (a b r s m : K) (hs : s ≠ 0)
    (hcurve : s^2=r^3+a*r+b) (hslope : 2*s*m=3*r^2+a) :
    curveCubic a b ∣ (doublingResidue a r s m)^2-(C (m^2-2*r)-X) := by
  refine ⟨(X+C (2*r))*C s⁻¹^2,?_⟩
  rw [polynomial_tangent_residue a b r s m hs hcurve hslope]
  ring

theorem square_residue_mul (f u v A B : K[X]) (hu : f ∣ u^2-A) (hv : f ∣ v^2-B) :
    f ∣ (u*v)^2-A*B := by
  obtain ⟨k,hk⟩ := hu
  obtain ⟨l,hl⟩ := hv
  refine ⟨k*v^2+A*l,?_⟩
  linear_combination v^2*hk+A*hl

theorem square_residue_product {I : Type*} (s : Finset I) (f : K[X]) (u A : I → K[X])
    (h : ∀ i ∈ s, f ∣ (u i)^2-A i) : f ∣ (∏ i ∈ s, u i)^2-∏ i ∈ s, A i := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro h
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact square_residue_mul f _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

theorem doubled_point_product_residue {I : Type*} (s : Finset I) (a b : K) (r y m : I → K)
    (hy : ∀ i ∈ s, y i ≠ 0) (hcurve : ∀ i ∈ s, (y i)^2=(r i)^3+a*r i+b)
    (hslope : ∀ i ∈ s, 2*y i*m i=3*(r i)^2+a) :
    curveCubic a b ∣ (∏ i ∈ s, doublingResidue a (r i) (y i) (m i))^2-
      ∏ i ∈ s, (C ((m i)^2-2*r i)-X) :=
  square_residue_product s _ _ _ (fun i hi ↦
    doubled_abscissa_square_residue a b (r i) (y i) (m i) (hy i hi) (hcurve i hi) (hslope i hi))

theorem cubic_reduce_square_residue (a b : K) (U A : K[X])
    (h : curveCubic a b ∣ U^2-A) :
    ∃ V : K[X], V.natDegree ≤ 2 ∧ curveCubic a b ∣ V^2-A := by
  let f := curveCubic a b
  let V := U %ₘ f
  have hd : f ∣ V-U := Polynomial.dvd_modByMonic_sub U f
  obtain ⟨k,hk⟩ := hd
  have hs : f ∣ V^2-U^2 := by
    refine ⟨k*(V+U),?_⟩
    linear_combination (V+U)*hk
  have hv : f ∣ V^2-A := by
    have he : V^2-A=(V^2-U^2)+(U^2-A) := by ring
    rw [he]
    exact dvd_add hs h
  have hf1 : f ≠ 1 := by
    intro he
    have hn := curveCubic_natDegree a b
    change f.natDegree=3 at hn
    rw [he,Polynomial.natDegree_one] at hn
    omega
  have hdeg := Polynomial.natDegree_modByMonic_lt U (CryptoLean.MonicNormSelector.curveCubic_monic a b) hf1
  change V.natDegree < f.natDegree at hdeg
  have hfd : f.natDegree=3 := curveCubic_natDegree a b
  exact ⟨V,by omega,hv⟩

theorem public_odd_half {G : Type*} [AddGroup G] (P : G) (q : ℕ)
    (hodd : q%2=1) (hq : q • P=0) :
    (q/2+1) • P+(q/2+1) • P=P := by
  have hd : 2*(q/2+1)=q+1 := by omega
  calc
    (q/2+1) • P+(q/2+1) • P=(q/2+1+(q/2+1)) • P := (add_nsmul _ _ _).symm
    _ = (2*(q/2+1)) • P := by congr 1; omega
    _ = (q+1) • P := by rw [hd]
    _ = P := by rw [add_nsmul,hq,one_nsmul,zero_add]

section ActualPoint
variable [DecidableEq K] {W : WeierstrassCurve.Affine K}

theorem short_tangent_interfaces (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (r s : K) (hs : s ≠ 0) (hR : W.Equation r s) :
    s ≠ W.negY r s ∧ s^2=r^3+W.a₄*r+W.a₆ ∧
      2*s*(W.slope r r s s)=3*r^2+W.a₄ ∧
      W.addX r r (W.slope r r s s)=(W.slope r r s s)^2-2*r := by
  have hneg : s ≠ W.negY r s := by
    intro he
    have he' : s= -s := by simpa [WeierstrassCurve.Affine.negY,ha1,ha3] using he
    have hz : 2*s=0 := by linear_combination he'
    exact mul_ne_zero htwo hs hz
  have hc : s^2=r^3+W.a₄*r+W.a₆ := by
    simpa [ha1,ha2,ha3] using (W.equation_iff r s).mp hR
  have hd : s-W.negY r s=2*s := by
    simp only [WeierstrassCurve.Affine.negY,ha1,ha3,zero_mul,sub_zero]
    ring
  have hm : W.slope r r s s=(3*r^2+W.a₄)/(2*s) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg,hd,ha2,ha1]
    simp
  refine ⟨hneg,hc,?_,?_⟩
  · rw [hm]
    field_simp
  · simp only [WeierstrassCurve.Affine.addX,ha1,ha2,zero_mul,add_zero,sub_zero]
    ring

theorem short_group_double_residue (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (r s : K) (hs : s ≠ 0) (hR : W.Nonsingular r s) :
    ((WeierstrassCurve.Affine.Point.some r s hR)+(.some r s hR)).xRep=
      ![W.addX r r (W.slope r r s s),1] ∧
    curveCubic W.a₄ W.a₆ ∣ (doublingResidue W.a₄ r s (W.slope r r s s))^2-
      (C (W.addX r r (W.slope r r s s))-X) := by
  have h := short_tangent_interfaces ha1 ha2 ha3 htwo r s hs hR.1
  constructor
  · rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne h.1,
      WeierstrassCurve.Affine.Point.xRep_some]
  · rw [h.2.2.2]
    exact doubled_abscissa_square_residue W.a₄ W.a₆ r s (W.slope r r s s) hs h.2.1 h.2.2.1

theorem odd_point_square_residue (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (P : W.Point) (hP : P ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : q • P=0) :
    ∃ xP : K, ∃ U : K[X], P.xRep= ![xP,1] ∧ curveCubic W.a₄ W.a₆ ∣ U^2-(C xP-X) := by
  let H := (q/2+1) • P
  have hH : H+H=P := public_odd_half P q hodd hq
  generalize heH : H=D at hH
  cases D with
  | zero =>
    change (0:W.Point)+(0:W.Point)=P at hH
    have hz : P=0 := by simpa using hH.symm
    exact False.elim (hP hz)
  | some r s hR =>
    have hs : s ≠ 0 := by
      intro hz
      have hn : s=W.negY r s := by simp [hz,WeierstrassCurve.Affine.negY,ha1,ha3]
      have hp0 := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁:=hR) hn
      exact hP (hH.symm.trans hp0)
    have hd := short_group_double_residue ha1 ha2 ha3 htwo r s hs hR
    exact ⟨W.addX r r (W.slope r r s s),doublingResidue W.a₄ r s (W.slope r r s s),
      by rw [← hH]; exact hd.1,hd.2⟩

theorem bounded_odd_point_square_residue (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (P : W.Point) (hP : P ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : q • P=0) :
    ∃ xP : K, ∃ U : K[X], P.xRep= ![xP,1] ∧ U.natDegree ≤ 2 ∧
      curveCubic W.a₄ W.a₆ ∣ U^2-(C xP-X) := by
  obtain ⟨xP,U,hx,hU⟩ := odd_point_square_residue ha1 ha2 ha3 htwo P hP q hodd hq
  obtain ⟨V,hdeg,hV⟩ := cubic_reduce_square_residue W.a₄ W.a₆ U (C xP-X) hU
  exact ⟨xP,V,hx,hdeg,hV⟩

theorem every_colored_odd_tuple_passes_residue {t b : ℕ}
    (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0) (htwo : (2:K) ≠ 0)
    (P : Fin t × Fin b → W.Point) (hP : ∀ p, P p ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : ∀ p, q • P p=0) :
    ∃ x : Fin t × Fin b → K, (∀ p, (P p).xRep= ![x p,1]) ∧
      ∀ choice : Fin t → Fin b, ∃ U : K[X], U.natDegree ≤ 2 ∧
        curveCubic W.a₄ W.a₆ ∣ U^2-∏ i : Fin t, (C (x (i,choice i))-X) := by
  classical
  choose x U hx hU using (fun p ↦ odd_point_square_residue ha1 ha2 ha3 htwo (P p) (hP p) q hodd (hq p))
  refine ⟨x,hx,?_⟩
  intro choice
  have hr := square_residue_product Finset.univ (curveCubic W.a₄ W.a₆)
    (fun i : Fin t ↦ U (i,choice i)) (fun i : Fin t ↦ C (x (i,choice i))-X)
    (fun i _ ↦ hU (i,choice i))
  exact cubic_reduce_square_residue W.a₄ W.a₆ _ _ hr

end ActualPoint

end CryptoLean.DoublingNormResidues
