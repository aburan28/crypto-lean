import CryptoLean.Polynomial.InterpolationKernels
import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-! Tight norm degree removes paired-point interpolation padding.
This does not construct a colored selector or prove its cost or group yield. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.NormSaturatedInterpolation
open Polynomial
variable {K : Type*} [Field K]

def curveCubic (a b : K) : K[X] := X^3+C a*X+C b
def curveNorm (a b : K) (u v : K[X]) : K[X] := u^2-curveCubic a b*v^2

theorem curveCubic_natDegree (a b : K) : (curveCubic a b).natDegree=3 := by
  simpa [curveCubic] using (Polynomial.natDegree_cubic (a:=(1:K)) (b:=0)
    (c:=a) (d:=b) one_ne_zero)

theorem curveCubic_ne_zero (a b : K) : curveCubic a b ≠ 0 := by
  intro h
  have hd := curveCubic_natDegree a b
  rw [h] at hd
  simp at hd

theorem curveNorm_eq_zero_iff (a b : K) (u v : K[X]) :
    curveNorm a b u v=0 ↔ u=0 ∧ v=0 := by
  constructor
  · intro hz
    have he : u^2=curveCubic a b*v^2 := sub_eq_zero.mp hz
    by_cases hv : v=0
    · simp only [hv,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] at he
      have hu : u=0 := by
        by_contra hu
        exact pow_ne_zero 2 hu he
      exact ⟨hu,hv⟩
    · have hedeg := congrArg Polynomial.natDegree he
      rw [Polynomial.natDegree_pow,Polynomial.natDegree_mul (curveCubic_ne_zero a b)
        (pow_ne_zero 2 hv),curveCubic_natDegree,Polynomial.natDegree_pow] at hedeg
      omega
  · rintro ⟨rfl,rfl⟩
    simp [curveNorm]

theorem curveNorm_nonzero (a b : K) (u v : K[X]) (h : (u,v) ≠ 0) :
    curveNorm a b u v ≠ 0 := by
  intro hz
  obtain ⟨hu,hv⟩ := (curveNorm_eq_zero_iff a b u v).mp hz
  exact h (by simp [hu,hv])

theorem curveNorm_eval (a b x y : K) (u v : K[X])
    (hcurve : y^2=x^3+a*x+b) :
    (curveNorm a b u v).eval x=(u.eval x+y*v.eval x)*(u.eval x-y*v.eval x) := by
  simp only [curveNorm,curveCubic,eval_sub,eval_mul,eval_pow,eval_add,eval_X,eval_C]
  rw [← hcurve]
  ring

theorem selected_norm_root (a b x y : K) (u v : K[X])
    (hcurve : y^2=x^3+a*x+b) (hrow : u.eval x+y*v.eval x=0) :
    (curveNorm a b u v).eval x=0 := by
  rw [curveNorm_eval a b x y u v hcurve,hrow,zero_mul]

theorem curveNorm_degree_bound (a b : K) (u v : K[X]) (t : ℕ)
    (hu : 2*u.natDegree ≤ t) (hv : 3+2*v.natDegree ≤ t) :
    (curveNorm a b u v).natDegree ≤ t := by
  have h₁ : (u^2).natDegree ≤ t := by
    simpa only [Polynomial.natDegree_pow] using hu
  have h₂ : (curveCubic a b*v^2).natDegree ≤ t :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [curveCubic_natDegree,Polynomial.natDegree_pow] using hv)
  simpa only [curveNorm,max_self] using Polynomial.natDegree_sub_le_of_le h₁ h₂

theorem tight_roots (p : K[X]) (S : Finset K) (hp : p ≠ 0)
    (heval : ∀ x ∈ S, p.eval x=0) (hdegree : p.natDegree ≤ S.card) :
    p.roots=S.val ∧ p.natDegree=S.card := by
  have hr := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero heval hdegree hp
  refine ⟨hr,le_antisymm hdegree ?_⟩
  have h := Polynomial.card_roots' p
  simpa only [hr,Finset.card] using h

theorem simple_roots_exclude_common_zero (a b : K) (u v : K[X])
    (S : Finset K) (hn : curveNorm a b u v ≠ 0)
    (hr : (curveNorm a b u v).roots=S.val) (x : K) :
    ¬ (u.eval x=0 ∧ v.eval x=0) := by
  classical
  rintro ⟨hu,hv⟩
  obtain ⟨u',hu'⟩ := (Polynomial.dvd_iff_isRoot).mpr hu
  obtain ⟨v',hv'⟩ := (Polynomial.dvd_iff_isRoot).mpr hv
  have hd : (X-C x)^2 ∣ curveNorm a b u v := by
    refine ⟨curveNorm a b u' v',?_⟩
    rw [hu',hv']
    simp only [curveNorm]
    ring
  have hcount : 2 ≤ S.val.count x := by
    simpa [hr] using Multiset.count_le_of_le x (Polynomial.roots.le_of_dvd hn hd)
  have hS : S.val.count x ≤ 1 := Multiset.nodup_iff_count_le_one.mp S.nodup x
  omega

theorem signed_coordinate_decode (x y : K) (u v : K[X])
    (hrow : u.eval x+y*v.eval x=0) (hv : v.eval x ≠ 0) :
    y= -u.eval x/v.eval x := by
  apply (eq_div_iff hv).2
  linear_combination hrow

theorem opposite_sign_not_selected (x y : K) (u v : K[X])
    (h₂ : (2:K) ≠ 0) (hy : y ≠ 0) (hv : v.eval x ≠ 0)
    (hrow : u.eval x+y*v.eval x=0) : u.eval x-y*v.eval x ≠ 0 := by
  intro hopp
  have he : 2*y*v.eval x=0 := by linear_combination hrow-hopp
  exact mul_ne_zero (mul_ne_zero h₂ hy) hv he

theorem tight_curve_certificate [DecidableEq K] {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (a b : K) (u v : K[X]) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i ∈ s, (y i)^2=(x i)^3+a*x i+b)
    (hrow : ∀ i ∈ s, u.eval (x i)+y i*v.eval (x i)=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ s.card) :
    (curveNorm a b u v).roots=(s.image x).val ∧
      (curveNorm a b u v).natDegree=s.card ∧
      (∀ z, ¬ (u.eval z=0 ∧ v.eval z=0)) ∧
      ∀ i ∈ s, v.eval (x i) ≠ 0 ∧ y i= -u.eval (x i)/v.eval (x i) := by
  classical
  have hn := curveNorm_nonzero a b u v hne
  have hc : (s.image x).card=s.card := Finset.card_image_of_injOn hx
  have he : ∀ z ∈ s.image x, (curveNorm a b u v).eval z=0 := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact selected_norm_root a b (x i) (y i) u v (hcurve i hi) (hrow i hi)
  have ht := tight_roots (curveNorm a b u v) (s.image x) hn he (hdegree.trans_eq hc.symm)
  have hcommon := simple_roots_exclude_common_zero a b u v (s.image x) hn ht.1
  refine ⟨ht.1,ht.2.trans hc,hcommon,?_⟩
  intro i hi
  have hv : v.eval (x i) ≠ 0 := by
    intro hz
    apply hcommon (x i)
    exact ⟨by simpa only [hz,mul_zero,add_zero] using hrow i hi,hz⟩
  exact ⟨hv,signed_coordinate_decode (x i) (y i) u v (hrow i hi) hv⟩

theorem tight_curve_certificate_of_caps [DecidableEq K] {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (a b : K) (u v : K[X]) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i ∈ s, (y i)^2=(x i)^3+a*x i+b)
    (hrow : ∀ i ∈ s, u.eval (x i)+y i*v.eval (x i)=0)
    (hu : 2*u.natDegree ≤ s.card) (hv : 3+2*v.natDegree ≤ s.card) :
    (curveNorm a b u v).roots=(s.image x).val ∧
      ∀ i ∈ s, v.eval (x i) ≠ 0 ∧ y i= -u.eval (x i)/v.eval (x i) := by
  have h := tight_curve_certificate s x y hx a b u v hne hcurve hrow
    (curveNorm_degree_bound a b u v s.card hu hv)
  exact ⟨h.1,h.2.2.2⟩

theorem tight_curve_zero_locus [DecidableEq K] {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (a b : K) (u v : K[X]) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i ∈ s, (y i)^2=(x i)^3+a*x i+b)
    (hrow : ∀ i ∈ s, u.eval (x i)+y i*v.eval (x i)=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ s.card) (z w : K)
    (hw : w^2=z^3+a*z+b) :
    u.eval z+w*v.eval z=0 ↔ ∃ i ∈ s, z=x i ∧ w=y i := by
  classical
  have ht := tight_curve_certificate s x y hx a b u v hne hcurve hrow hdegree
  constructor
  · intro hz
    have hm : z ∈ (curveNorm a b u v).roots :=
      (Polynomial.mem_roots (curveNorm_nonzero a b u v hne)).mpr
        (selected_norm_root a b z w u v hw hz)
    rw [ht.1] at hm
    obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hm
    refine ⟨i,hi,hix.symm,?_⟩
    rw [← hix] at hz
    exact (signed_coordinate_decode (x i) w u v hz (ht.2.2.2 i hi).1).trans
      (ht.2.2.2 i hi).2.symm
  · rintro ⟨i,hi,rfl,rfl⟩
    exact hrow i hi

theorem tight_norm_factorization (a b : K) (u v : K[X]) (S : Finset K)
    (hne : (u,v) ≠ 0) (heval : ∀ x ∈ S, (curveNorm a b u v).eval x=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ S.card) :
    curveNorm a b u v=C (curveNorm a b u v).leadingCoeff*Lagrange.nodal S id := by
  have ht := tight_roots (curveNorm a b u v) S (curveNorm_nonzero a b u v hne) heval hdegree
  have hc : (curveNorm a b u v).roots.card=(curveNorm a b u v).natDegree := by
    rw [ht.1,ht.2]
    rfl
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  rw [ht.1] at h
  exact h.symm

theorem tight_norm_square_congruence (a b : K) (u v : K[X]) (S : Finset K)
    (hne : (u,v) ≠ 0) (heval : ∀ x ∈ S, (curveNorm a b u v).eval x=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ S.card) :
    curveCubic a b ∣ u^2-C (curveNorm a b u v).leadingCoeff*Lagrange.nodal S id := by
  have h := tight_norm_factorization a b u v S hne heval hdegree
  refine ⟨v^2,?_⟩
  rw [← h]
  simp only [curveNorm]
  ring

theorem polynomial_X_not_square (v : K[X]) : v^2 ≠ X := by
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_pow,Polynomial.natDegree_X] at hd
  omega

theorem cubic_congruence_false_positive (a b : K) :
    curveCubic a b ∣ (0 : K[X])^2-(-curveCubic a b*X) ∧
      ¬ ∃ v : K[X], curveNorm a b 0 v= -curveCubic a b*X := by
  constructor
  · refine ⟨X,?_⟩
    ring
  · rintro ⟨v,hv⟩
    have he : curveCubic a b*v^2=curveCubic a b*X := by
      simpa only [curveNorm,zero_pow (by decide : (2:ℕ) ≠ 0),zero_sub,
        neg_mul,neg_inj] using hv
    exact polynomial_X_not_square v (mul_left_cancel₀ (curveCubic_ne_zero a b) he)

theorem pure_nodal_norm_degree {I : Type*} (s : Finset I) (x : I → K) (a b : K) :
    (curveNorm a b (Lagrange.nodal s x) 0).natDegree=2*s.card := by
  simp [curveNorm,Polynomial.natDegree_pow]

theorem nonempty_pure_nodal_rejected {I : Type*} (s : Finset I) (x : I → K)
    (a b : K) (hs : 0 < s.card) :
    ¬ (curveNorm a b (Lagrange.nodal s x) 0).natDegree ≤ s.card := by
  rw [pure_nodal_norm_degree]
  omega

theorem pure_u_kernel_zero_above_cap {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (dU dV : ℕ) (ht : dU < s.card) (u : K[X])
    (h : (u,0) ∈ CryptoLean.InterpolationKernels.kernel x y dU dV s) : u=0 := by
  classical
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' u (s.image x)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    simpa using h.2.2 i hi
  · rw [Finset.card_image_of_injOn hx]
    exact h.1.trans_lt ht

theorem kernel_same_v_unique_u {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (dU dV : ℕ) (ht : dU < s.card) (u u' v : K[X])
    (h : (u,v) ∈ CryptoLean.InterpolationKernels.kernel x y dU dV s)
    (h' : (u',v) ∈ CryptoLean.InterpolationKernels.kernel x y dU dV s) : u=u' := by
  classical
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' u u' (s.image x)
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    linear_combination h.2.2 i hi-h'.2.2 i hi
  · rw [Finset.card_image_of_injOn hx]
    exact max_lt_iff.mpr ⟨h.1.trans_lt ht,h'.1.trans_lt ht⟩

theorem kernel_second_injective {I : Type*} (s : Finset I) (x y : I → K)
    (hx : Set.InjOn x s) (dU dV : ℕ) (ht : dU < s.card) :
    Function.Injective (fun uv : {uv // uv ∈ CryptoLean.InterpolationKernels.kernel x y dU dV s}
      ↦ uv.val.2) := by
  rintro ⟨⟨u,v⟩,h⟩ ⟨⟨u',v'⟩,h'⟩ heq
  dsimp at heq
  subst v'
  have hu := kernel_same_v_unique_u s x y hx dU dV ht u u' v h h'
  apply Subtype.ext
  exact Prod.ext hu rfl

theorem tight_cap_above_pure_u_range (dU t : ℕ) (ht : 0 < t) (hcap : 2*dU ≤ t) :
    dU < t := by omega

end CryptoLean.NormSaturatedInterpolation
