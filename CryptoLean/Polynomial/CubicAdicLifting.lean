import CryptoLean.Polynomial.DoublingNormResidues

/-! Unit square-root lifts and the information limit of bare cubic-adic tests.
No fast degree-restricted reconstruction or ECDLP algorithm is asserted. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.CubicAdicLifting
open Polynomial CryptoLean.NormSaturatedInterpolation CryptoLean.DoublingNormResidues
variable {R : Type*} [CommRing R]

theorem inverse_residue_transport (f u u0 w : R)
    (hres : f ∣ u-u0) (hinv : f ∣ 2*u0*w-1) : f ∣ 2*u*w-1 := by
  obtain ⟨a,ha⟩ := hres
  obtain ⟨b,hb⟩ := hinv
  refine ⟨2*w*a+b,?_⟩
  linear_combination 2*w*ha+hb

theorem unit_square_root_step (f u g w : R) (n : ℕ)
    (hroot : f^(n+1) ∣ u^2-g) (hinv : f ∣ 2*u*w-1) :
    ∃ v : R, f^(n+2) ∣ v^2-g ∧ f ∣ v-u := by
  obtain ⟨a,ha⟩ := hroot
  obtain ⟨b,hb⟩ := hinv
  refine ⟨u-f^(n+1)*w*a,?_,?_⟩
  · refine ⟨-b*a+f^n*w^2*a^2,?_⟩
    simp only [pow_succ] at ha ⊢
    linear_combination ha-(f^n*f*a)*hb
  · refine ⟨-f^n*w*a,?_⟩
    rw [pow_succ]
    ring

theorem unit_square_root_all_precisions (f u0 g w : R)
    (hroot : f ∣ u0^2-g) (hinv : f ∣ 2*u0*w-1) :
    ∀ n : ℕ, ∃ u : R, f^(n+1) ∣ u^2-g ∧ f ∣ u-u0 := by
  intro n
  induction n with
  | zero => exact ⟨u0,by simpa using hroot,by simp⟩
  | succ n ih =>
    obtain ⟨u,hu,hres⟩ := ih
    have hi := inverse_residue_transport f u u0 w hres hinv
    obtain ⟨v,hv,hchange⟩ := unit_square_root_step f u g w n hu hi
    refine ⟨v,by simpa only [Nat.add_assoc] using hv,?_⟩
    have he : v-u0=(v-u)+(u-u0) := by ring
    rw [he]
    exact dvd_add hchange hres

theorem unit_square_root_power (f u0 g w : R) (k : ℕ) (hk : 0 < k)
    (hroot : f ∣ u0^2-g) (hinv : f ∣ 2*u0*w-1) :
    ∃ u : R, f^k ∣ u^2-g ∧ f ∣ u-u0 := by
  have he : k-1+1=k := by omega
  simpa only [he] using unit_square_root_all_precisions f u0 g w hroot hinv (k-1)

theorem inverse_from_square (f u g v t : R) (ht : 2*t=1)
    (hroot : f ∣ u^2-g) (hunit : f ∣ g*v-1) : f ∣ 2*u*(t*u*v)-1 := by
  obtain ⟨a,ha⟩ := hroot
  obtain ⟨b,hb⟩ := hunit
  have he : 2*u*(t*u*v)=u^2*v := by
    calc
      2*u*(t*u*v)=(2*t)*u^2*v := by ring
      _ = u^2*v := by rw [ht,one_mul]
  rw [he]
  refine ⟨a*v+b,?_⟩
  linear_combination v*ha+hb

theorem residue_inverse_mul (f a A b B : R) (ha : f ∣ a*A-1) (hb : f ∣ b*B-1) :
    f ∣ (a*b)*(A*B)-1 := by
  obtain ⟨c,hc⟩ := ha
  obtain ⟨d,hd⟩ := hb
  refine ⟨c*b*B+d,?_⟩
  linear_combination b*B*hc+hd

theorem residue_inverse_product {I : Type*} (s : Finset I) (f : R) (a A : I → R)
    (h : ∀ i ∈ s, f ∣ a i*A i-1) : f ∣ (∏ i ∈ s, a i)*(∏ i ∈ s, A i)-1 := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro h
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact residue_inverse_mul f _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

theorem abscissa_factor_identity (a b x y z : R) (hcurve : y^2=x^3+a*x+b) :
    (x-z)*(z^2+x*z+x^2+a)=y^2-(z^3+a*z+b) := by
  linear_combination -hcurve

variable {K : Type*} [Field K]

def abscissaInverse (a x y : K) : K[X] :=
  (X^2+C x*X+C (x^2+a))*C y⁻¹^2

theorem abscissa_inverse_residue (a b x y : K) (hy : y ≠ 0)
    (hcurve : y^2=x^3+a*x+b) :
    curveCubic a b ∣ (C x-X)*abscissaInverse a x y-1 := by
  have hc : (C y : K[X])^2=(C x)^3+C a*C x+C b := by
    simpa only [map_pow,map_add,map_mul] using congrArg (C : K →+* K[X]) hcurve
  have h := @abscissa_factor_identity (Polynomial K) (@Polynomial.commRing K inferInstance)
    (C a) (C b) (C x) (C y) X hc
  have hQ : (C (x^2+a) : K[X])=(C x)^2+C a := by rw [map_add,map_pow]
  have hi : (C y : K[X])^2*(C y⁻¹)^2=1 := by
    rw [← mul_pow,← map_mul,mul_inv_cancel₀ hy,map_one,one_pow]
  refine ⟨-(C y⁻¹)^2,?_⟩
  unfold abscissaInverse curveCubic
  rw [hQ]
  calc
    (C x-X)*((X^2+C x*X+((C x)^2+C a))*C y⁻¹^2)-1 =
      ((C x-X)*(X^2+C x*X+(C x)^2+C a))*C y⁻¹^2-1 := by ring
    _ = ((C y)^2-(X^3+C a*X+C b))*C y⁻¹^2-1 := by rw [h]
    _ = (X^3+C a*X+C b)*(-(C y⁻¹)^2) := by rw [sub_mul,hi]; ring

theorem reduce_monic_square_residue (f U g : K[X]) (hf : f.Monic) (hf1 : f ≠ 1)
    (h : f ∣ U^2-g) : ∃ V : K[X], V.natDegree < f.natDegree ∧ f ∣ V^2-g := by
  let V := U %ₘ f
  obtain ⟨a,ha⟩ := Polynomial.dvd_modByMonic_sub U f
  have hd : f ∣ V^2-U^2 := by
    refine ⟨a*(V+U),?_⟩
    linear_combination (V+U)*ha
  have he : V^2-g=(V^2-U^2)+(U^2-g) := by ring
  refine ⟨V,Polynomial.natDegree_modByMonic_lt U hf hf1,?_⟩
  rw [he]
  exact dvd_add hd h

theorem cubic_unit_roots_all_powers (a b : K) (u0 g v : K[X]) (htwo : (2:K) ≠ 0)
    (hroot : curveCubic a b ∣ u0^2-g) (hunit : curveCubic a b ∣ g*v-1)
    (k : ℕ) (hk : 0 < k) :
    ∃ U : K[X], U.natDegree < 3*k ∧ (curveCubic a b)^k ∣ U^2-g := by
  have ht : (2:K[X])*C ((2:K)⁻¹)=1 := by
    simpa only [map_mul,map_ofNat,map_one] using
      congrArg (C : K →+* K[X]) (mul_inv_cancel₀ htwo)
  have hi := inverse_from_square (curveCubic a b) u0 g v (C ((2:K)⁻¹)) ht hroot hunit
  obtain ⟨u,hu,_⟩ := unit_square_root_power (curveCubic a b) u0 g _ k hk hroot hi
  have hf : ((curveCubic a b)^k).Monic := (CryptoLean.MonicNormSelector.curveCubic_monic a b).pow k
  have hd : ((curveCubic a b)^k).natDegree=3*k := by
    rw [Polynomial.natDegree_pow,curveCubic_natDegree,Nat.mul_comm]
  have hf1 : (curveCubic a b)^k ≠ 1 := by
    intro he
    rw [he,Polynomial.natDegree_one] at hd
    omega
  obtain ⟨U,hdeg,hU⟩ := reduce_monic_square_residue _ u g hf hf1 hu
  exact ⟨U,hdeg.trans_eq hd,hU⟩

theorem cubic_unit_roots_below_cap (a b : K) (u0 g v : K[X]) (htwo : (2:K) ≠ 0)
    (hroot : curveCubic a b ∣ u0^2-g) (hunit : curveCubic a b ∣ g*v-1)
    (k d : ℕ) (hk : 0 < k) (hcap : 3*k ≤ d+1) :
    ∃ U : K[X], U.natDegree ≤ d ∧ (curveCubic a b)^k ∣ U^2-g := by
  obtain ⟨U,hdeg,hU⟩ := cubic_unit_roots_all_powers a b u0 g v htwo hroot hunit k hk
  exact ⟨U,by omega,hU⟩

theorem odd_ann_double_ne_zero {G : Type*} [AddCommGroup G] (P : G) (hP : P ≠ 0)
    (q : ℕ) (hodd : q%2=1) (hq : q • P=0) : P+P ≠ 0 := by
  intro hz
  have hh := public_odd_half P q hodd hq
  have he : (q/2+1) • P+(q/2+1) • P=0 := by
    calc
      (q/2+1) • P+(q/2+1) • P=(q/2+1) • (P+P) := (nsmul_add _ _ _).symm
      _ = 0 := by rw [hz,nsmul_zero]
  exact hP (hh.symm.trans he)

section ActualPoint
variable [DecidableEq K] {W : WeierstrassCurve.Affine K}

theorem odd_point_unit_coordinates (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (P : W.Point) (hP : P ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : q • P=0) :
    ∃ x y : K, P.xRep= ![x,1] ∧ y^2=x^3+W.a₄*x+W.a₆ ∧ y ≠ 0 := by
  cases P with
  | zero =>
    change (0:W.Point) ≠ 0 at hP
    exact False.elim (hP rfl)
  | some x y hR =>
    have hy : y ≠ 0 := by
      intro hz
      have hn : y=W.negY x y := by simp [hz,WeierstrassCurve.Affine.negY,ha1,ha3]
      have hd := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁:=hR) hn
      exact odd_ann_double_ne_zero (WeierstrassCurve.Affine.Point.some x y hR) hP q hodd hq hd
    have hc := (short_tangent_interfaces ha1 ha2 ha3 htwo x y hy hR.1).2.1
    exact ⟨x,y,WeierstrassCurve.Affine.Point.xRep_some hR,hc,hy⟩

theorem odd_point_unit_square (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0)
    (htwo : (2:K) ≠ 0) (P : W.Point) (hP : P ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : q • P=0) :
    ∃ x y : K, ∃ U : K[X], P.xRep= ![x,1] ∧ y^2=x^3+W.a₄*x+W.a₆ ∧ y ≠ 0 ∧
      curveCubic W.a₄ W.a₆ ∣ U^2-(C x-X) := by
  obtain ⟨x,U,hx,hU⟩ := odd_point_square_residue ha1 ha2 ha3 htwo P hP q hodd hq
  obtain ⟨x',y,hx',hc,hy⟩ := odd_point_unit_coordinates ha1 ha2 ha3 htwo P hP q hodd hq
  have he : x=x' := by
    have h := congrArg (fun z : Fin 2 → K ↦ z 0) (hx.symm.trans hx')
    simpa using h
  subst x'
  exact ⟨x,y,U,hx,hc,hy,hU⟩

theorem every_colored_odd_tuple_all_powers {t b : ℕ}
    (ha1 : W.a₁=0) (ha2 : W.a₂=0) (ha3 : W.a₃=0) (htwo : (2:K) ≠ 0)
    (P : Fin t × Fin b → W.Point) (hP : ∀ p, P p ≠ 0) (q : ℕ)
    (hodd : q%2=1) (hq : ∀ p, q • P p=0) :
    ∃ x : Fin t × Fin b → K, (∀ p, (P p).xRep= ![x p,1]) ∧
      ∀ choice : Fin t → Fin b, ∀ k : ℕ, 0 < k →
        ∃ U : K[X], U.natDegree < 3*k ∧
          (curveCubic W.a₄ W.a₆)^k ∣ U^2-∏ i : Fin t, (C (x (i,choice i))-X) := by
  classical
  choose x y U hx hc hy hU using
    (fun p ↦ odd_point_unit_square ha1 ha2 ha3 htwo (P p) (hP p) q hodd (hq p))
  refine ⟨x,hx,?_⟩
  intro choice k hk
  have hroot := square_residue_product Finset.univ (curveCubic W.a₄ W.a₆)
    (fun i : Fin t ↦ U (i,choice i)) (fun i : Fin t ↦ C (x (i,choice i))-X)
    (fun i _ ↦ hU (i,choice i))
  have hunit := residue_inverse_product Finset.univ (curveCubic W.a₄ W.a₆)
    (fun i : Fin t ↦ C (x (i,choice i))-X)
    (fun i : Fin t ↦ abscissaInverse W.a₄ (x (i,choice i)) (y (i,choice i)))
    (fun i _ ↦ abscissa_inverse_residue W.a₄ W.a₆ _ _ (hy (i,choice i)) (hc (i,choice i)))
  exact cubic_unit_roots_all_powers W.a₄ W.a₆ _ _ _ htwo hroot hunit k hk

end ActualPoint

theorem nonunit_X_control :
    (X : K[X]) ∣ (0:K[X])^2-X ∧ ¬ ∃ U : K[X], X^2 ∣ U^2-X := by
  constructor
  · exact ⟨-1,by ring⟩
  · rintro ⟨U,h⟩
    have hLift := h
    obtain ⟨v,hv⟩ := h
    have he := congrArg (fun p : K[X] ↦ p.eval 0) hv
    simp only [eval_sub,eval_pow,eval_X,eval_mul,zero_pow (by decide : (2:ℕ) ≠ 0),
      zero_mul,sub_zero] at he
    have hu : U.eval 0=0 := by
      by_contra hz
      exact pow_ne_zero 2 hz he
    have hX : (X : K[X]) ∣ U := by
      simpa using (Polynomial.dvd_iff_isRoot).mpr hu
    obtain ⟨a,ha⟩ := hX
    have hpow : (X : K[X])^2 ∣ U^2 := ⟨a^2,by rw [ha]; ring⟩
    have hd : (X : K[X])^2 ∣ X := by
      have hsub := dvd_sub hpow hLift
      have hid : U^2-(U^2-X)=X := by ring
      simpa only [hid] using hsub
    have hdeg := Polynomial.natDegree_le_of_dvd hd (Polynomial.X_ne_zero (R:=K))
    norm_num [Polynomial.natDegree_pow] at hdeg

theorem one_sub_cubic_degree (a b : K) : (1-curveCubic a b).natDegree=3 := by
  have hlt : (1:K[X]).natDegree < (curveCubic a b).natDegree := by
    rw [Polynomial.natDegree_one,curveCubic_natDegree]
    decide
  exact (Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt).trans (curveCubic_natDegree a b)

theorem one_sub_cubic_not_square (a b : K) (U : K[X]) : U^2 ≠ 1-curveCubic a b := by
  intro he
  have hd := congrArg Polynomial.natDegree he
  rw [Polynomial.natDegree_pow,one_sub_cubic_degree] at hd
  omega

theorem cubic_power_small_degree_zero (a b : K) (E : K[X]) (k t : ℕ)
    (hdeg : E.natDegree ≤ t) (hprecision : t < 3*k)
    (hdiv : (curveCubic a b)^k ∣ E) : E=0 := by
  by_contra he
  have hd := Polynomial.natDegree_le_of_dvd hdiv he
  rw [Polynomial.natDegree_pow,curveCubic_natDegree] at hd
  omega

theorem bounded_full_norm_precision_iff (a b : K) (u v g : K[X]) (k t : ℕ)
    (hu : 2*u.natDegree ≤ t) (hv : 3+2*v.natDegree ≤ t) (hg : g.natDegree ≤ t)
    (hprecision : t < 3*k) :
    ((curveCubic a b)^k ∣ curveNorm a b u v-g) ↔ curveNorm a b u v=g := by
  constructor
  · intro h
    have hn := curveNorm_degree_bound a b u v t hu hv
    have hd : (curveNorm a b u v-g).natDegree ≤ t := by
      simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hn hg
    exact sub_eq_zero.mp (cubic_power_small_degree_zero a b _ k t hd hprecision h)
  · intro he
    rw [he,sub_self]
    exact dvd_zero _

theorem capped_lift_rejects_full_norm (a b : K) :
    ¬ ∃ U : K[X], U.natDegree ≤ 2 ∧
      (curveCubic a b)^2 ∣ U^2-(1-curveCubic a b) := by
  rintro ⟨U,hU,hdiv⟩
  have hu : (U^2).natDegree ≤ 4 := by rw [Polynomial.natDegree_pow]; omega
  have hg : (1-curveCubic a b).natDegree ≤ 4 := by rw [one_sub_cubic_degree]; decide
  have hd : (U^2-(1-curveCubic a b)).natDegree ≤ 4 := by
    simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hu hg
  have hz := cubic_power_small_degree_zero a b _ 2 4 hd (by decide) hdiv
  exact one_sub_cubic_not_square a b U (sub_eq_zero.mp hz)

theorem full_norm_without_capped_root (a b : K) :
    curveNorm a b 1 1=1-curveCubic a b ∧
      curveCubic a b ∣ (1:K[X])^2-(1-curveCubic a b) ∧
      ¬ ∃ U : K[X], U.natDegree ≤ 2 ∧
        (curveCubic a b)^2 ∣ U^2-(1-curveCubic a b) := by
  refine ⟨by simp [curveNorm],⟨1,by ring⟩,capped_lift_rejects_full_norm a b⟩

theorem horizontal_norm_family (r s : K) :
    curveNorm (-(r^2+r*s+s^2)) (1+r*s*(r+s)) 1 1 =
      -((X-C r)*(X-C s)*(X+C (r+s))) := by
  simp only [curveNorm,curveCubic,map_add,map_mul,map_pow,map_neg,map_one]
  ring

theorem horizontal_curve_records (r s : K) (i : Fin 3) :
    let x : Fin 3 → K := ![r,s,-(r+s)]
    (-1:K)^2=(x i)^3+(-(r^2+r*s+s^2))*x i+(1+r*s*(r+s)) ∧
      (1:K[X]).eval (x i)+(-1)*(1:K[X]).eval (x i)=0 := by
  fin_cases i <;> dsimp <;> constructor
  all_goals ring

end CryptoLean.CubicAdicLifting
