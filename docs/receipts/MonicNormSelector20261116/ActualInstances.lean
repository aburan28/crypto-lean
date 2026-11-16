import CryptoLean.Polynomial.MonicNormSelector

set_option autoImplicit false
noncomputable section
open Polynomial CryptoLean.NormSaturatedInterpolation CryptoLean.MonicNormSelector

namespace MonicNormActual
variable {K : Type*} [Field K]

theorem actual_curve_row_normalization [DecidableEq K] {I : Type*}
    (s : Finset I) (x y : I → K) (hx : Set.InjOn x s) (a b : K) (u v : K[X])
    (hne : (u,v) ≠ 0) (hcurve : ∀ i ∈ s, (y i)^2=(x i)^3+a*x i+b)
    (hrow : ∀ i ∈ s, u.eval (x i)+y i*v.eval (x i)=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ s.card) :
    ∃ q : K[X], q ≠ 0 ∧ (normalizeBy q q).Monic ∧
      (normalizeBy q u).natDegree=u.natDegree ∧
      (normalizeBy q v).natDegree=v.natDegree ∧
      (∀ i ∈ s, (normalizeBy q u).eval (x i)+y i*(normalizeBy q v).eval (x i)=0) ∧
      (curveNorm a b (normalizeBy q u) (normalizeBy q v)=Lagrange.nodal (s.image x) id ∨
       curveNorm a b (normalizeBy q u) (normalizeBy q v)= -Lagrange.nodal (s.image x) id) := by
  have hc : (s.image x).card=s.card := Finset.card_image_of_injOn hx
  have he : ∀ z ∈ s.image x, (curveNorm a b u v).eval z=0 := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact selected_norm_root a b (x i) (y i) u v (hcurve i hi) (hrow i hi)
  have ht := tight_monic_normal_form a b u v (s.image x) hne he (hdegree.trans_eq hc.symm)
  rcases ht with ⟨hu,hm,hn,_⟩ | ⟨hv,hm,hn,_⟩
  · exact ⟨u,hu,hm,normalization_degree u u hu,normalization_degree u v hu,
      fun i hi ↦ (normalization_row_iff u u v hu (x i) (y i)).mpr (hrow i hi),Or.inl hn⟩
  · exact ⟨v,hv,hm,normalization_degree v u hv,normalization_degree v v hv,
      fun i hi ↦ (normalization_row_iff v u v hv (x i) (y i)).mpr (hrow i hi),Or.inr hn⟩

theorem actual_normalized_color_filters [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (hx : Function.Injective x) (a c : K) (q u v : K[X])
    (hq : q ≠ 0) (hne : (u,v) ≠ 0)
    (hcurve : ∀ i j, (y (i,j))^2=(x (i,j))^3+a*x (i,j)+c)
    (hproducts : ∀ i, CryptoLean.InterpolationKernels.colorProduct x y i u v=0)
    (hdegree : (curveNorm a c u v).natDegree ≤ t) :
    ∃ choice : Fin t → Fin b, ∀ i,
      zeroChoices x y (normalizeBy q u) (normalizeBy q v) i={choice i} := by
  obtain ⟨choice,hchoice⟩ := tight_zeroChoices_singletons x y hx a c u v hne hcurve hproducts hdegree
  exact ⟨choice,fun i ↦ (normalization_zeroChoices x y q u v hq i).trans (hchoice i)⟩

theorem empty_constant_normal_form (a b c : K) (hc : c ≠ 0) :
    normalizeBy (C c) (C c)=1 ∧
      curveNorm a b (normalizeBy (C c) (C c)) (normalizeBy (C c) 0)=1 := by
  have hn : normalizeBy (C c) (C c)=1 := by
    simp [normalizeBy,← map_mul,hc]
  refine ⟨hn,?_⟩
  rw [hn]
  simp [normalizeBy,curveNorm]

theorem zero_u_has_odd_norm_shape (a b : K) (v : K[X]) (hv : v ≠ 0) :
    (curveNorm a b 0 v).natDegree=3+2*v.natDegree ∧
      (curveNorm a b 0 v).leadingCoeff= -v.leadingCoeff^2 := by
  have hne : ((0:K[X]),v) ≠ 0 := by
    intro hz
    exact hv (congrArg Prod.snd hz)
  rcases norm_leading_shape a b 0 v hne with ⟨h,_,_⟩ | ⟨_,hd,hl⟩
  · exact False.elim (h rfl)
  · exact ⟨hd,hl⟩

theorem zero_pair_keeps_all_factors [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (i : Fin t) :
    (zeroChoices x y 0 0 i).card=b := by
  simp [zeroChoices]

theorem empty_color_constant_choice [DecidableEq K] {b : ℕ}
    (x y : Fin 0 × Fin b → K) (a c : K) :
    ∃! choice : Fin 0 → Fin b, ∀ i,
      (1:K[X]).eval (x (i,choice i))+y (i,choice i)*(0:K[X]).eval (x (i,choice i))=0 := by
  have hx : Function.Injective x := by intro p; exact Fin.elim0 p.1
  apply tight_color_unique_choice x y hx a c 1 0
  · simp
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · simp [curveNorm]

end MonicNormActual
