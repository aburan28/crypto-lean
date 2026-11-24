import CryptoLean.Polynomial.NormSaturatedInterpolation

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.NormSaturatedInterpolation CryptoLean.InterpolationKernels

namespace NormSaturatedActual
variable {K : Type*} [Field K]

theorem colorful_signed_zero_locus [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (hx : Function.Injective x) (choice : Fin t → Fin b)
    (a c : K) (u v : K[X]) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i j, (y (i,j))^2=(x (i,j))^3+a*x (i,j)+c)
    (hrow : ∀ i, u.eval (x (i,choice i))+y (i,choice i)*v.eval (x (i,choice i))=0)
    (hu : 2*u.natDegree ≤ t) (hv : 3+2*v.natDegree ≤ t) (z w : K)
    (hw : w^2=z^3+a*z+c) :
    u.eval z+w*v.eval z=0 ↔ ∃ i, z=x (i,choice i) ∧ w=y (i,choice i) := by
  have hr : ∀ p ∈ prefixSupport choice, u.eval (x p)+y p*v.eval (x p)=0 := by
    rintro ⟨i,j⟩ hp
    have hj := (mem_prefixSupport choice i j).mp hp
    subst j
    exact hrow i
  have hc : ∀ p ∈ prefixSupport choice, (y p)^2=(x p)^3+a*x p+c := by
    rintro ⟨i,j⟩ _
    exact hcurve i j
  have ht := tight_curve_zero_locus (prefixSupport choice) x y hx.injOn a c u v hne hc hr
    (by simpa only [prefixSupport_card] using curveNorm_degree_bound a c u v t hu hv) z w hw
  rw [ht]
  constructor
  · rintro ⟨⟨i,j⟩,hp,hz,hw'⟩
    have hj := (mem_prefixSupport choice i j).mp hp
    subst j
    exact ⟨i,hz,hw'⟩
  · rintro ⟨i,hz,hw'⟩
    exact ⟨(i,choice i),(mem_prefixSupport choice i (choice i)).mpr rfl,hz,hw'⟩

theorem tight_row_excludes_opposite {I : Type*} [DecidableEq K]
    (s : Finset I) (x y : I → K) (hx : Set.InjOn x s) (a b : K)
    (u v : K[X]) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i ∈ s, (y i)^2=(x i)^3+a*x i+b)
    (hrow : ∀ i ∈ s, u.eval (x i)+y i*v.eval (x i)=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ s.card)
    (h₂ : (2:K) ≠ 0) (i : I) (hi : i ∈ s) (hy : y i ≠ 0) :
    u.eval (x i)-y i*v.eval (x i) ≠ 0 := by
  have ht := tight_curve_certificate s x y hx a b u v hne hcurve hrow hdegree
  exact opposite_sign_not_selected (x i) (y i) u v h₂ hy (ht.2.2.2 i hi).1 (hrow i hi)

theorem duplicate_curve_node_padding (a b r s : K) (hcurve : s^2=r^3+a*r+b) :
    (∀ _i : Fin 2, s^2=r^3+a*r+b ∧
      (X-C r : K[X]).eval r+s*(0:K[X]).eval r=0) ∧
    (curveNorm a b (X-C r) 0).natDegree ≤ (Finset.univ : Finset (Fin 2)).card ∧
      (0:K[X]).eval r=0 := by
  refine ⟨fun _ ↦ ⟨hcurve,by simp⟩,?_,by simp⟩
  simp [curveNorm,Polynomial.natDegree_pow]

theorem empty_constant_is_retained (a b : K) :
    curveNorm a b 1 0=1 ∧
      (curveNorm a b 1 0).natDegree ≤ (∅ : Finset K).card ∧
      (1:K[X]) ≠ 0 := by
  simp [curveNorm]

theorem useful_caps_second_projection_injective {I : Type*}
    (s : Finset I) (x y : I → K) (hx : Set.InjOn x s) (dU dV : ℕ)
    (hs : 0 < s.card) (hcap : 2*dU ≤ s.card) :
    Function.Injective (fun uv : {uv // uv ∈ kernel x y dU dV s} ↦ uv.val.2) :=
  kernel_second_injective s x y hx dU dV (tight_cap_above_pure_u_range dU s.card hs hcap)

end NormSaturatedActual
