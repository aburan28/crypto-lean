import CryptoLean.Polynomial.NormSaturatedInterpolation

/-! Complete scalar normalization and exact supplied-row color filters.
No fast nonzero discovery or elliptic group-yield claim. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.MonicNormSelector
open Polynomial CryptoLean.NormSaturatedInterpolation CryptoLean.InterpolationKernels
variable {K : Type*} [Field K]

def normalizeBy (q p : K[X]) : K[X] := p*C q.leadingCoeff⁻¹

theorem curveCubic_monic (a b : K) : (curveCubic a b).Monic := by
  change (curveCubic a b).leadingCoeff=1
  simpa [curveCubic] using (Polynomial.leadingCoeff_cubic (a:=(1:K)) (b:=0)
    (c:=a) (d:=b) one_ne_zero)

theorem curveNorm_scale (a b scalar : K) (u v : K[X]) :
    curveNorm a b (u*C scalar) (v*C scalar)=C (scalar^2)*curveNorm a b u v := by
  simp only [curveNorm,map_pow]
  ring

theorem row_scale (x y scalar : K) (u v : K[X]) :
    (u*C scalar).eval x+y*(v*C scalar).eval x=scalar*(u.eval x+y*v.eval x) := by
  simp only [eval_mul,eval_C]
  ring

theorem normalization_monic (q : K[X]) (hq : q ≠ 0) : (normalizeBy q q).Monic :=
  Polynomial.monic_mul_leadingCoeff_inv hq

theorem normalization_degree (q p : K[X]) (hq : q ≠ 0) :
    (normalizeBy q p).natDegree=p.natDegree :=
  Polynomial.natDegree_mul_leadingCoeff_inv p hq

theorem normalization_recover (q p : K[X]) (hq : q ≠ 0) :
    normalizeBy q p*C q.leadingCoeff=p := by
  have hc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  simp only [normalizeBy,mul_assoc,← map_mul,inv_mul_cancel₀ hc,map_one,mul_one]

theorem normalization_row_iff (q u v : K[X]) (hq : q ≠ 0) (x y : K) :
    (normalizeBy q u).eval x+y*(normalizeBy q v).eval x=0 ↔
      u.eval x+y*v.eval x=0 := by
  rw [normalizeBy,normalizeBy,row_scale]
  exact mul_eq_zero.trans (or_iff_right (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq)))

theorem norm_leading_shape (a b : K) (u v : K[X]) (hne : (u,v) ≠ 0) :
    (u ≠ 0 ∧ (curveNorm a b u v).natDegree=2*u.natDegree ∧
      (curveNorm a b u v).leadingCoeff=u.leadingCoeff^2) ∨
    (v ≠ 0 ∧ (curveNorm a b u v).natDegree=3+2*v.natDegree ∧
      (curveNorm a b u v).leadingCoeff= -v.leadingCoeff^2) := by
  by_cases hv : v=0
  · have hu : u ≠ 0 := by
      intro hu
      exact hne (by simp [hu,hv])
    left
    exact ⟨hu,by simp [curveNorm,hv,Polynomial.natDegree_pow],
      by simp [curveNorm,hv,Polynomial.leadingCoeff_pow]⟩
  have hdq : (curveCubic a b*v^2).natDegree=3+2*v.natDegree := by
    rw [Polynomial.natDegree_mul (curveCubic_ne_zero a b) (pow_ne_zero 2 hv),
      curveCubic_natDegree,Polynomial.natDegree_pow]
  have hdp : (u^2).natDegree=2*u.natDegree := Polynomial.natDegree_pow u 2
  by_cases hd : 3+2*v.natDegree < 2*u.natDegree
  · have hlt : (curveCubic a b*v^2).natDegree < (u^2).natDegree := by omega
    have hu : u ≠ 0 := by
      intro hz
      simp only [hz,Polynomial.natDegree_zero,mul_zero] at hd
      omega
    left
    refine ⟨hu,?_,?_⟩
    · exact (Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt).trans hdp
    · rw [curveNorm,Polynomial.leadingCoeff_sub_of_degree_lt (Polynomial.degree_lt_degree hlt),
        Polynomial.leadingCoeff_pow]
  · have hlt : (u^2).natDegree < (curveCubic a b*v^2).natDegree := by omega
    right
    refine ⟨hv,?_,?_⟩
    · exact (Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt).trans hdq
    · rw [curveNorm,Polynomial.leadingCoeff_sub_of_degree_lt' (Polynomial.degree_lt_degree hlt),
        Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_pow,(curveCubic_monic a b).leadingCoeff,
        one_mul]

theorem normalized_even_norm (a b : K) (u v : K[X]) (hu : u ≠ 0) (g : K[X])
    (hfactor : curveNorm a b u v=C (curveNorm a b u v).leadingCoeff*g)
    (hlc : (curveNorm a b u v).leadingCoeff=u.leadingCoeff^2) :
    curveNorm a b (normalizeBy u u) (normalizeBy u v)=g := by
  have hc : u.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hu
  have hi : u.leadingCoeff⁻¹^2*u.leadingCoeff^2=1 := by
    rw [← mul_pow,inv_mul_cancel₀ hc,one_pow]
  rw [normalizeBy,normalizeBy,curveNorm_scale,hfactor,hlc,← mul_assoc,← map_mul,hi,map_one,one_mul]

theorem normalized_odd_norm (a b : K) (u v : K[X]) (hv : v ≠ 0) (g : K[X])
    (hfactor : curveNorm a b u v=C (curveNorm a b u v).leadingCoeff*g)
    (hlc : (curveNorm a b u v).leadingCoeff= -v.leadingCoeff^2) :
    curveNorm a b (normalizeBy v u) (normalizeBy v v)= -g := by
  have hc : v.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hv
  have hi : v.leadingCoeff⁻¹^2*(-v.leadingCoeff^2)= -1 := by
    rw [mul_neg,← mul_pow,inv_mul_cancel₀ hc,one_pow]
  rw [normalizeBy,normalizeBy,curveNorm_scale,hfactor,hlc,← mul_assoc,← map_mul,hi,map_neg,map_one,
    neg_one_mul]

theorem tight_monic_normal_form (a b : K) (u v : K[X]) (S : Finset K)
    (hne : (u,v) ≠ 0) (heval : ∀ x ∈ S, (curveNorm a b u v).eval x=0)
    (hdegree : (curveNorm a b u v).natDegree ≤ S.card) :
    (u ≠ 0 ∧ (normalizeBy u u).Monic ∧
      curveNorm a b (normalizeBy u u) (normalizeBy u v)=Lagrange.nodal S id ∧
      S.card=2*u.natDegree) ∨
    (v ≠ 0 ∧ (normalizeBy v v).Monic ∧
      curveNorm a b (normalizeBy v u) (normalizeBy v v)= -Lagrange.nodal S id ∧
      S.card=3+2*v.natDegree) := by
  have hf := tight_norm_factorization a b u v S hne heval hdegree
  have ht := tight_roots (curveNorm a b u v) S (curveNorm_nonzero a b u v hne) heval hdegree
  rcases norm_leading_shape a b u v hne with ⟨hu,hd,hl⟩ | ⟨hv,hd,hl⟩
  · exact Or.inl ⟨hu,normalization_monic u hu,normalized_even_norm a b u v hu _ hf hl,
      ht.2.symm.trans hd⟩
  · exact Or.inr ⟨hv,normalization_monic v hv,normalized_odd_norm a b u v hv _ hf hl,
      ht.2.symm.trans hd⟩

theorem tight_color_zero_graph [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (hx : Function.Injective x) (a c : K) (u v : K[X])
    (hne : (u,v) ≠ 0) (hcurve : ∀ i j, (y (i,j))^2=(x (i,j))^3+a*x (i,j)+c)
    (hproducts : ∀ i, colorProduct x y i u v=0)
    (hdegree : (curveNorm a c u v).natDegree ≤ t) :
    ∃ choice : Fin t → Fin b, ∀ i j,
      u.eval (x (i,j))+y (i,j)*v.eval (x (i,j))=0 ↔ j=choice i := by
  obtain ⟨choice,hchoice⟩ := (colorProducts_zero_iff_choice x y u v).mp hproducts
  have hr : ∀ p ∈ prefixSupport choice, u.eval (x p)+y p*v.eval (x p)=0 := by
    rintro ⟨i,j⟩ hp
    have hj := (mem_prefixSupport choice i j).mp hp
    subst j
    exact hchoice i
  have hc : ∀ p ∈ prefixSupport choice, (y p)^2=(x p)^3+a*x p+c := by
    rintro ⟨i,j⟩ _
    exact hcurve i j
  refine ⟨choice,?_⟩
  intro i j
  constructor
  · intro hz
    have h := (tight_curve_zero_locus (prefixSupport choice) x y hx.injOn a c u v hne hc hr
      (by simpa only [prefixSupport_card] using hdegree) (x (i,j)) (y (i,j)) (hcurve i j)).mp hz
    obtain ⟨p,hp,he,_⟩ := h
    have hpair : (i,j)=p := hx he
    have hm : (i,j) ∈ prefixSupport choice := by rw [hpair]; exact hp
    exact (mem_prefixSupport choice i j).mp hm
  · intro hj
    subst j
    exact hchoice i

theorem tight_color_unique_choice [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (hx : Function.Injective x) (a c : K) (u v : K[X])
    (hne : (u,v) ≠ 0) (hcurve : ∀ i j, (y (i,j))^2=(x (i,j))^3+a*x (i,j)+c)
    (hproducts : ∀ i, colorProduct x y i u v=0)
    (hdegree : (curveNorm a c u v).natDegree ≤ t) :
    ∃! choice : Fin t → Fin b, ∀ i,
      u.eval (x (i,choice i))+y (i,choice i)*v.eval (x (i,choice i))=0 := by
  obtain ⟨choice,hchoice⟩ := tight_color_zero_graph x y hx a c u v hne hcurve hproducts hdegree
  refine ⟨choice,fun i ↦ (hchoice i (choice i)).mpr rfl,?_⟩
  intro other hother
  funext i
  exact (hchoice i (other i)).mp (hother i)

def zeroChoices [DecidableEq K] {t b : ℕ} (x y : Fin t × Fin b → K)
    (u v : K[X]) (i : Fin t) : Finset (Fin b) :=
  Finset.univ.filter (fun j ↦ u.eval (x (i,j))+y (i,j)*v.eval (x (i,j))=0)

theorem tight_zeroChoices_singletons [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (hx : Function.Injective x) (a c : K) (u v : K[X])
    (hne : (u,v) ≠ 0) (hcurve : ∀ i j, (y (i,j))^2=(x (i,j))^3+a*x (i,j)+c)
    (hproducts : ∀ i, colorProduct x y i u v=0)
    (hdegree : (curveNorm a c u v).natDegree ≤ t) :
    ∃ choice : Fin t → Fin b, ∀ i, zeroChoices x y u v i={choice i} := by
  obtain ⟨choice,hchoice⟩ := tight_color_zero_graph x y hx a c u v hne hcurve hproducts hdegree
  refine ⟨choice,?_⟩
  intro i
  ext j
  simp only [zeroChoices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  exact hchoice i j

theorem normalization_zeroChoices [DecidableEq K] {t b : ℕ}
    (x y : Fin t × Fin b → K) (q u v : K[X]) (hq : q ≠ 0) (i : Fin t) :
    zeroChoices x y (normalizeBy q u) (normalizeBy q v) i=zeroChoices x y u v i := by
  ext j
  simp only [zeroChoices,Finset.mem_filter,Finset.mem_univ,true_and]
  exact normalization_row_iff q u v hq (x (i,j)) (y (i,j))

end CryptoLean.MonicNormSelector
