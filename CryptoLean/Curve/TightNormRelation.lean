import CryptoLean.Polynomial.NormSaturatedInterpolation
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import CryptoLean.Group.SingleRelation

/-! Tight affine interpolation rows and actual elliptic-curve relations.
This is an output certificate; it does not find a useful row quickly. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Polynomial.Bivariate nonZeroDivisors

namespace CryptoLean.TightNormRelation
open Polynomial WeierstrassCurve.Affine
variable {K : Type*} [Field K]

theorem ideal_eq_of_le_equal_quotient_dimension {A : Type*} [CommRing A]
    [Algebra K A] (I J : Ideal A) (hle : I ≤ J)
    (hdim : Module.finrank K (A ⧸ I) = Module.finrank K (A ⧸ J))
    (hpos : 0 < Module.finrank K (A ⧸ I)) : I = J := by
  let := Module.finite_of_finrank_pos hpos
  let := Module.finite_of_finrank_pos (hdim ▸ hpos)
  let f : (A ⧸ I) →ₐ[K] A ⧸ J := Ideal.quotientMapₐ J (AlgHom.id K A) hle
  have hs : Function.Surjective f :=
    Ideal.quotientMap_surjective (H := hle) Function.surjective_id
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mpr hs
  apply le_antisymm hle
  intro a ha
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  apply hi
  rw [map_zero]
  change Ideal.Quotient.mk J a = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

noncomputable def coprimeQuotientEquiv {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (I : ι → Ideal A)
    (hc : Pairwise (fun i j ↦ IsCoprime (I i) (I j))) :
    (A ⧸ ⨅ i, I i) ≃ₐ[K] ∀ i, A ⧸ I i :=
  AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient I hc) (by
    intro k
    ext i
    rfl)

theorem coprime_quotient_dimension {A : Type*} [CommRing A] [Algebra K A]
    {ι : Type*} [Fintype ι] (I : ι → Ideal A)
    (hc : Pairwise (fun i j ↦ IsCoprime (I i) (I j)))
    (he : ∀ i, (A ⧸ I i) ≃ₐ[K] K) :
    Module.finrank K (A ⧸ ⨅ i, I i) = Fintype.card ι := by
  let (i : ι) : Module.Finite K (A ⧸ I i) :=
    Module.Finite.equiv (he i).symm.toLinearEquiv
  rw [(coprimeQuotientEquiv I hc).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  simp only [fun i ↦ (he i).toLinearEquiv.finrank_eq, Module.finrank_self,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

variable (W : WeierstrassCurve.Affine K)

def rowFunction (u v : K[X]) : W.CoordinateRing :=
  u • (1 : W.CoordinateRing) + v • CoordinateRing.mk W Y

theorem rowFunction_nonzero (u v : K[X]) (hp : (u,v) ≠ 0) :
    rowFunction W u v ≠ 0 := by
  intro hz
  obtain ⟨hu,hv⟩ := CoordinateRing.smul_basis_eq_zero hz
  exact hp (by simp [hu,hv])

theorem rowFunction_mem_pointIdeal (u v : K[X]) (x y : K)
    (hr : u.eval x+y*v.eval x=0) :
    rowFunction W u v ∈ CoordinateRing.XYIdeal W x (C y) := by
  have hm : C u+C v*Y ∈ Ideal.span {C (X-C x), Y-C (C y)} := by
    apply Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr
    simpa only [eval_add,eval_C,eval_mul,eval_X,mul_comm] using hr
  have hmap := Ideal.mem_map_of_mem (CoordinateRing.mk W) hm
  simpa only [rowFunction, CoordinateRing.smul, mul_one, map_add, map_mul,
    Ideal.map_span, Set.image_pair, CoordinateRing.XYIdeal, CoordinateRing.XClass,
    CoordinateRing.YClass] using hmap

theorem pointIdeals_coprime (x₁ x₂ y₁ y₂ : K) (hx : x₁ ≠ x₂) :
    IsCoprime (CoordinateRing.XYIdeal W x₁ (C y₁))
      (CoordinateRing.XYIdeal W x₂ (C y₂)) := by
  let c := CoordinateRing.mk W (C (C ((x₂-x₁)⁻¹)))
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨c*CoordinateRing.XClass W x₁, Ideal.mul_mem_left _ _
    (Ideal.subset_span (by simp)), -c*CoordinateRing.XClass W x₂,
    Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)), ?_⟩
  have hi : (x₂-x₁)⁻¹*(x₂-x₁)=1 := inv_mul_cancel₀ (sub_ne_zero.mpr hx.symm)
  calc
    c*CoordinateRing.XClass W x₁ + -c*CoordinateRing.XClass W x₂ =
      CoordinateRing.mk W (C (C ((x₂-x₁)⁻¹)*((X-C x₁)-(X-C x₂)))) := by
        simp only [c, CoordinateRing.XClass, map_mul, map_sub]
        ring
    _ = 1 := by
      have hp : C ((x₂-x₁)⁻¹)*((X-C x₁)-(X-C x₂)) = (1 : K[X]) := by
        calc
          _ = C ((x₂-x₁)⁻¹*(x₂-x₁)) := by simp only [C_mul,C_sub]; ring
          _ = 1 := by rw [hi, C_1]
      rw [hp, C_1, map_one]

theorem tight_row_ideal_product {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → K) (hx : Function.Injective x)
    (hc : ∀ i, W.Nonsingular (x i) (y i)) (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x i)+y i*v.eval (x i)=0)
    (hd : (Algebra.norm K[X] (rowFunction W u v)).natDegree=Fintype.card ι) :
    (∏ i, CoordinateRing.XYIdeal W (x i) (C (y i))) =
      Ideal.span {rowFunction W u v} := by
  classical
  let I (i : ι) := CoordinateRing.XYIdeal W (x i) (C (y i))
  have hcp : Pairwise (fun i j ↦ IsCoprime (I i) (I j)) :=
    fun i j hij ↦ pointIdeals_coprime W (x i) (x j) (y i) (y j) (hx.ne hij)
  have hprod : (∏ i, I i) = ⨅ i, I i := by
    simpa using (Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := I)
      (fun i _ j _ hij ↦ hcp hij))
  have hle : Ideal.span {rowFunction W u v} ≤ ⨅ i, I i := by
    refine le_iInf (fun i ↦ (Ideal.span_singleton_le_iff_mem _).mpr ?_)
    exact rowFunction_mem_pointIdeal W u v (x i) (y i) (hr i)
  have hdim₁ : Module.finrank K (W.CoordinateRing ⧸ Ideal.span {rowFunction W u v}) =
      Fintype.card ι :=
    (finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W)
      (rowFunction_nonzero W u v hp)).trans hd
  have hdim₂ : Module.finrank K (W.CoordinateRing ⧸ ⨅ i, I i) = Fintype.card ι :=
    coprime_quotient_dimension I hcp (fun i ↦ CoordinateRing.quotientXYIdealEquiv (hc i).left)
  have he := ideal_eq_of_le_equal_quotient_dimension
    (Ideal.span {rowFunction W u v}) (⨅ i, I i) hle (hdim₁.trans hdim₂.symm)
    (by rw [hdim₁]; exact Fintype.card_pos)
  exact hprod.trans he.symm

variable [DecidableEq K]

theorem point_sum_of_principal_product {ι : Type*} [Fintype ι]
    (x y : ι → K) (hc : ∀ i, W.Nonsingular (x i) (y i))
    (f : W.CoordinateRing) (hf : f ≠ 0)
    (hp : (∏ i, CoordinateRing.XYIdeal W (x i) (C (y i))) = Ideal.span {f}) :
    (∑ i, (Point.some (x i) (y i) (hc i) : W.Point)) = 0 := by
  classical
  let J (i : ι) := CoordinateRing.XYIdeal' (W := W) (hc i)
  have hcoe : (↑(∏ i, J i) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) =
      (∏ i, CoordinateRing.XYIdeal W (x i) (C (y i))) := by
    rw [Units.coe_prod]
    exact (map_prod (FractionalIdeal.coeIdealHom W.CoordinateRing⁰ W.FunctionField)
      (fun i ↦ CoordinateRing.XYIdeal W (x i) (C (y i))) Finset.univ).symm
  have hcl := (ClassGroup.mk_eq_one_of_coe_ideal hcoe).mpr ⟨f,hf,hp⟩
  apply Point.toClass_injective
  rw [map_sum, map_zero]
  change (∑ i, Additive.ofMul (ClassGroup.mk W.FunctionField (J i))) = 0
  change Additive.ofMul (∏ i, ClassGroup.mk W.FunctionField (J i)) = 0
  rw [← map_prod, hcl]
  rfl

theorem tight_row_sum_zero {ι : Type*} [Fintype ι]
    (x y : ι → K) (hx : Function.Injective x)
    (hc : ∀ i, W.Nonsingular (x i) (y i)) (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x i)+y i*v.eval (x i)=0)
    (hd : (Algebra.norm K[X] (rowFunction W u v)).natDegree=Fintype.card ι) :
    (∑ i, (Point.some (x i) (y i) (hc i) : W.Point)) = 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    exact point_sum_of_principal_product W x y hc (rowFunction W u v)
      (rowFunction_nonzero W u v hp) (tight_row_ideal_product W x y hx hc u v hp hr hd)

omit [DecidableEq K] in
theorem short_norm_eq (ha₁ : W.a₁=0) (ha₂ : W.a₂=0) (ha₃ : W.a₃=0)
    (u v : K[X]) : Algebra.norm K[X] (rowFunction W u v) =
      CryptoLean.NormSaturatedInterpolation.curveNorm W.a₄ W.a₆ u v := by
  rw [rowFunction, CoordinateRing.norm_smul_basis]
  simp only [ha₁,ha₂,ha₃,C_0,mul_zero,sub_zero,zero_mul,add_zero]
  unfold CryptoLean.NormSaturatedInterpolation.curveNorm
    CryptoLean.NormSaturatedInterpolation.curveCubic
  ring

theorem short_tight_row_sum_zero {ι : Type*} [Fintype ι]
    (ha₁ : W.a₁=0) (ha₂ : W.a₂=0) (ha₃ : W.a₃=0)
    (x y : ι → K) (hx : Function.Injective x)
    (hc : ∀ i, W.Nonsingular (x i) (y i)) (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x i)+y i*v.eval (x i)=0)
    (hd : (CryptoLean.NormSaturatedInterpolation.curveNorm W.a₄ W.a₆ u v).natDegree ≤
      Fintype.card ι) :
    (∑ i, (Point.some (x i) (y i) (hc i) : W.Point)) = 0 := by
  classical
  have ht := CryptoLean.NormSaturatedInterpolation.tight_curve_certificate Finset.univ x y
    hx.injOn W.a₄ W.a₆ u v hp
    (fun i _ ↦ by simpa [ha₁,ha₂,ha₃] using (W.equation_iff (x i) (y i)).mp (hc i).left)
    (fun i _ ↦ hr i) (by simpa only [Finset.card_univ] using hd)
  apply tight_row_sum_zero W x y hx hc u v hp hr
  rw [short_norm_eq W ha₁ ha₂ ha₃]
  simpa only [Finset.card_univ] using ht.2.1

theorem short_capped_row_sum_zero {ι : Type*} [Fintype ι]
    (ha₁ : W.a₁=0) (ha₂ : W.a₂=0) (ha₃ : W.a₃=0)
    (x y : ι → K) (hx : Function.Injective x)
    (hc : ∀ i, W.Nonsingular (x i) (y i)) (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x i)+y i*v.eval (x i)=0)
    (hu : 2*u.natDegree ≤ Fintype.card ι)
    (hv : 3+2*v.natDegree ≤ Fintype.card ι) :
    (∑ i, (Point.some (x i) (y i) (hc i) : W.Point)) = 0 := by
  exact short_tight_row_sum_zero W ha₁ ha₂ ha₃ x y hx hc u v hp hr
    (CryptoLean.NormSaturatedInterpolation.curveNorm_degree_bound W.a₄ W.a₆ u v _ hu hv)

omit W [DecidableEq K] in
theorem recover_nat_mixed_relation {A : Type*} [AddCommGroup A]
    {ι : Type*} [Fintype ι] (G H : A) (q k : ℕ) [Fact q.Prime]
    (ho : addOrderOf G=q) (hH : H=k • G) (α β : ι → ℕ)
    (hr : (∑ i, (α i • G+β i • H))=0)
    (hb : (∑ i, (β i : ZMod q)) ≠ 0) :
    -(∑ i, (α i : ZMod q))/(∑ i, (β i : ZMod q))=(k : ZMod q) := by
  have he (i : ι) : α i • G+β i • H=(α i+k*β i) • G := by
    rw [hH, ← mul_nsmul, add_nsmul]
  simp_rw [he] at hr
  rw [Finset.sum_nsmul_assoc] at hr
  have hd : q ∣ ∑ i, (α i+k*β i) := by
    rw [← ho]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hr
  have hz : (∑ i, ((α i : ZMod q)+(k : ZMod q)*(β i : ZMod q)))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_add,Nat.cast_mul] using
      (ZMod.natCast_eq_zero_iff (∑ i, (α i+k*β i)) q).mpr hd
  simpa only [one_mul] using CryptoLean.SingleRelation.recover_from_relation
    Finset.univ (fun i ↦ (α i : ZMod q)) (fun i ↦ (β i : ZMod q))
    (fun _ ↦ (1 : ZMod q)) (k : ZMod q) (by simpa only [one_mul] using hz)
    (by simpa only [one_mul] using hb)

theorem recover_from_short_tight_row {ι : Type*} [Fintype ι]
    (ha₁ : W.a₁=0) (ha₂ : W.a₂=0) (ha₃ : W.a₃=0)
    (G H : W.Point) (q k : ℕ) [Fact q.Prime] (ho : addOrderOf G=q) (hH : H=k • G)
    (α β : ι → ℕ) (x y : ι → K) (hx : Function.Injective x)
    (hc : ∀ i, W.Nonsingular (x i) (y i))
    (hm : ∀ i, (Point.some (x i) (y i) (hc i) : W.Point)=α i • G+β i • H)
    (u v : K[X]) (hp : (u,v) ≠ 0)
    (hr : ∀ i, u.eval (x i)+y i*v.eval (x i)=0)
    (hd : (CryptoLean.NormSaturatedInterpolation.curveNorm W.a₄ W.a₆ u v).natDegree ≤
      Fintype.card ι) (hb : (∑ i, (β i : ZMod q)) ≠ 0) :
    -(∑ i, (α i : ZMod q))/(∑ i, (β i : ZMod q))=(k : ZMod q) := by
  have hz := short_tight_row_sum_zero W ha₁ ha₂ ha₃ x y hx hc u v hp hr hd
  simp_rw [hm] at hz
  exact recover_nat_mixed_relation G H q k ho hH α β hz hb

end CryptoLean.TightNormRelation
