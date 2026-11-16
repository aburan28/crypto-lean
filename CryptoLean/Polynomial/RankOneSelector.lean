import CryptoLean.Combinatorics.FieldRectangles
import CryptoLean.Polynomial.ShortCoefficientWindows
import Mathlib.Data.ZMod.ValMinAbs

/-! Complete norm-short existence search in a declared rank-one modular row
family, using two coefficient windows. No useful ECDLP yield theorem. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.RankOneSelector
open CryptoLean.FieldRectangles CryptoLean.ShortCoefficientWindows
variable {ι : Type*} [Fintype ι]
variable (p : ℕ) [Fact p.Prime]

def rowNorm (weight : ι → ℕ) (row : ι → ℤ) : ℕ :=
  ∑ i, (row i).natAbs*weight i

def centeredRow (scalar : ZMod p) (F : ι → ZMod p) : ι → ℤ :=
  fun i ↦ (scalar*F i).valMinAbs

omit [Fintype ι] in
theorem centered_cast (scalar : ZMod p) (F : ι → ZMod p) (i : ι) :
    (centeredRow p scalar F i : ZMod p)=scalar*F i := ZMod.coe_valMinAbs _

theorem centered_norm_minimal (weight : ι → ℕ) (scalar : ZMod p)
    (F : ι → ZMod p) (row : ι → ℤ)
    (hrow : ∀ i, (row i : ZMod p)=scalar*F i) :
    rowNorm weight (centeredRow p scalar F) ≤ rowNorm weight row := by
  apply Finset.sum_le_sum
  intro i _
  apply Nat.mul_le_mul_right
  exact ZMod.natAbs_min_of_le_div_two p _ _
    ((centered_cast p scalar F i).trans (hrow i).symm)
    (ZMod.natAbs_valMinAbs_le _)

omit [Fact p.Prime] in
theorem coordinate_bound_of_short (n : ℕ) (weight : ι → ℕ) (row : ι → ℤ)
    (i : ι) (hcut : p ≤ (n+1)*weight i) (hshort : rowNorm weight row < p) :
    (row i).natAbs ≤ n := by
  have hterm : (row i).natAbs*weight i ≤ rowNorm weight row :=
    Finset.single_le_sum (f := fun j ↦ (row j).natAbs*weight j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  by_contra hn
  have hlarge : n+1 ≤ (row i).natAbs := by omega
  exact (Nat.not_lt_of_ge (hcut.trans
    ((Nat.mul_le_mul_right _ hlarge).trans hterm))) hshort

theorem integer_scalar_nonzero (scalar : ℤ) (weight : ι → ℕ)
    (hweight : ∀ i, 1 ≤ weight i) (row base F : ι → ℤ) (hne : row ≠ 0)
    (hrow : ∀ i, row i=(p : ℤ)*base i+scalar*F i)
    (hshort : rowNorm weight row < p) : (scalar : ZMod p) ≠ 0 := by
  intro hzero
  have hs := (ZMod.intCast_zmod_eq_zero_iff_dvd scalar p).mp hzero
  apply hne
  funext i
  change row i=0
  by_contra hc
  have hd : (p : ℤ) ∣ row i := by
    rw [hrow i]
    exact dvd_add (dvd_mul_right (p : ℤ) (base i)) (dvd_mul_of_dvd_left hs (F i))
  have hlarge : p ≤ (row i).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (Int.natCast_dvd.mp hd)
  have hterm : (row i).natAbs*weight i ≤ rowNorm weight row :=
    Finset.single_le_sum (f := fun j ↦ (row j).natAbs*weight j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
  have hbound : p ≤ rowNorm weight row := by
    calc
      p ≤ (row i).natAbs := hlarge
      _ = (row i).natAbs*1 := by simp
      _ ≤ (row i).natAbs*weight i := Nat.mul_le_mul_left _ (hweight i)
      _ ≤ _ := hterm
  exact (Nat.not_lt_of_ge hbound) hshort

omit [Fact p.Prime] in
theorem cutoff_of_positive (weight : ℕ) (hp : 0 < p) (hw : 0 < weight) :
    p ≤ ((p-1)/weight+1)*weight := by
  have he := Nat.mod_add_div (p-1) weight
  have hm := Nat.mod_lt (p-1) hw
  rw [Nat.mul_comm weight ((p-1)/weight)] at he
  rw [Nat.add_mul,one_mul]
  omega

def pairCandidates (scale center : ZMod p) (A B : Finset (ZMod p)) :
    Finset (ZMod p × ZMod p) :=
  ((A.erase 0) ×ˢ B).image (fun ab ↦ (ab.1,center+(scale*ab.1)⁻¹*ab.2))

theorem pairCandidates_card_le (scale center : ZMod p) (A B : Finset (ZMod p)) :
    (pairCandidates p scale center A B).card ≤ A.card*B.card := by
  calc
    _ ≤ ((A.erase 0) ×ˢ B).card := Finset.card_image_le
    _ = (A.erase 0).card*B.card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset 0 A))

theorem pairCandidates_scalar_ne_zero (scale center scalar offset : ZMod p)
    (A B : Finset (ZMod p)) (h : (scalar,offset) ∈ pairCandidates p scale center A B) :
    scalar ≠ 0 := by
  obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp h
  have ha := (Finset.mem_erase.mp (Finset.mem_product.mp hab).1).1
  have he : a=scalar := congrArg Prod.fst heq
  exact he ▸ ha

theorem pairCandidates_of_relation (scale center scalar offset : ZMod p)
    (hscale : scale ≠ 0) (hscalar : scalar ≠ 0) (A B : Finset (ZMod p))
    (hA : scalar ∈ A) (hB : scale*scalar*(offset-center) ∈ B) :
    (scalar,offset) ∈ pairCandidates p scale center A B := by
  refine Finset.mem_image.mpr ⟨(scalar,scale*scalar*(offset-center)),
    Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hscalar,hA⟩,hB⟩,?_⟩
  simp [mul_assoc,hscale,hscalar]

def selectedPairs (scale center : ZMod p) (a b : ℕ)
    (weight : ι → ℕ) (F : ZMod p → ι → ZMod p) : Finset (ZMod p × ZMod p) :=
  (pairCandidates p scale center (intWindow (ZMod p) a) (intWindow (ZMod p) b)).filter
    (fun pair ↦ rowNorm weight (centeredRow p pair.1 (F pair.2)) < p)

theorem selected_card_le (scale center : ZMod p) (a b : ℕ)
    (weight : ι → ℕ) (F : ZMod p → ι → ZMod p) :
    (selectedPairs p scale center a b weight F).card ≤ (2*a+1)*(2*b+1) := by
  calc
    _ ≤ (pairCandidates p scale center (intWindow (ZMod p) a)
      (intWindow (ZMod p) b)).card := Finset.card_filter_le _ _
    _ ≤ _ := (pairCandidates_card_le p scale center _ _).trans
      (Nat.mul_le_mul (intWindow_card_le a) (intWindow_card_le b))

theorem selected_sound (scale center scalar offset : ZMod p) (a b : ℕ)
    (weight : ι → ℕ) (F : ZMod p → ι → ZMod p)
    (h : (scalar,offset) ∈ selectedPairs p scale center a b weight F) :
    scalar ≠ 0 ∧ rowNorm weight (centeredRow p scalar (F offset)) < p ∧
      ∀ i, (centeredRow p scalar (F offset) i : ZMod p)=scalar*F offset i := by
  have hh := Finset.mem_filter.mp h
  exact ⟨pairCandidates_scalar_ne_zero p scale center scalar offset _ _ hh.1,
    hh.2,centered_cast p scalar (F offset)⟩

theorem selected_offset_in_rectangle (scale center scalar offset : ZMod p) (a b : ℕ)
    (weight : ι → ℕ) (F : ZMod p → ι → ZMod p)
    (h : (scalar,offset) ∈ selectedPairs p scale center a b weight F) :
    offset ∈ rectangleImage scale center (intWindow (ZMod p) a) (intWindow (ZMod p) b) := by
  obtain ⟨⟨c,d⟩,hcd,heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
  exact Finset.mem_image.mpr ⟨(c,d),hcd,congrArg Prod.snd heq⟩

theorem selected_complete (scale center scalar offset : ZMod p)
    (hscale : scale ≠ 0) (hscalar : scalar ≠ 0) (a b : ℕ)
    (weight : ι → ℕ) (F : ZMod p → ι → ZMod p) (i₁ i₂ : ι)
    (hfirst : F offset i₁=1) (hsecond : F offset i₂=scale*(offset-center))
    (hcut₁ : p ≤ (a+1)*weight i₁) (hcut₂ : p ≤ (b+1)*weight i₂)
    (row : ι → ℤ) (hrow : ∀ i, (row i : ZMod p)=scalar*F offset i)
    (hshort : rowNorm weight row < p) :
    (scalar,offset) ∈ selectedPairs p scale center a b weight F := by
  have hbound₁ := integer_bounds_of_natAbs a (row i₁)
    (coordinate_bound_of_short p a weight row i₁ hcut₁ hshort)
  have hbound₂ := integer_bounds_of_natAbs b (row i₂)
    (coordinate_bound_of_short p b weight row i₂ hcut₂ hshort)
  have hres₁ : (row i₁ : ZMod p)=scalar := by simpa only [hfirst,mul_one] using hrow i₁
  have hres₂ : (row i₂ : ZMod p)=scale*scalar*(offset-center) := by
    rw [hrow i₂,hsecond]
    ring
  apply Finset.mem_filter.mpr
  refine ⟨pairCandidates_of_relation p scale center scalar offset hscale hscalar _ _ ?_ ?_,
    (centered_norm_minimal p weight scalar (F offset) row hrow).trans_lt hshort⟩
  · rw [← hres₁]
    exact mem_intWindow_of_bounds a _ hbound₁
  · rw [← hres₂]
    exact mem_intWindow_of_bounds b _ hbound₂

omit [Fintype ι] in
theorem centered_nonzero (scalar : ZMod p) (hscalar : scalar ≠ 0)
    (F : ι → ZMod p) (i : ι) (hi : F i=1) : centeredRow p scalar F ≠ 0 := by
  intro hz
  have h := centered_cast p scalar F i
  rw [hz,Pi.zero_apply,Int.cast_zero,hi,mul_one] at h
  exact hscalar h.symm

omit [Fintype ι] in
theorem centered_integer_witness (scalar : ℤ) (F : ι → ℤ) :
    ∃ h : ι → ℤ, ∀ i,
      centeredRow p (scalar : ZMod p) (fun j ↦ (F j : ZMod p)) i =
        (p : ℤ)*h i+scalar*F i := by
  have hd (i : ι) : (p : ℤ) ∣
      centeredRow p (scalar : ZMod p) (fun j ↦ (F j : ZMod p)) i-scalar*F i := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simp only [Int.cast_sub,Int.cast_mul,centered_cast,sub_self]
  choose h hh using hd
  exact ⟨h,fun i ↦ by have := hh i; omega⟩

theorem selected_complete_integer (scale center offset : ZMod p) (scalar : ℤ)
    (hscale : scale ≠ 0) (a b : ℕ) (weight : ι → ℕ) (hweight : ∀ i, 1 ≤ weight i)
    (F : ZMod p → ι → ZMod p) (Fint row base : ι → ℤ)
    (hlift : ∀ i, (Fint i : ZMod p)=F offset i) (i₁ i₂ : ι)
    (hfirst : F offset i₁=1) (hsecond : F offset i₂=scale*(offset-center))
    (hcut₁ : p ≤ (a+1)*weight i₁) (hcut₂ : p ≤ (b+1)*weight i₂)
    (hne : row ≠ 0) (hrow : ∀ i, row i=(p : ℤ)*base i+scalar*Fint i)
    (hshort : rowNorm weight row < p) :
    ((scalar : ZMod p),offset) ∈ selectedPairs p scale center a b weight F := by
  apply selected_complete p scale center (scalar : ZMod p) offset hscale
    (integer_scalar_nonzero p scalar weight hweight row base Fint hne hrow hshort)
    a b weight F i₁ i₂ hfirst hsecond hcut₁ hcut₂ row ?_ hshort
  intro i
  rw [hrow i]
  push_cast
  simp only [ZMod.natCast_self,zero_mul,zero_add,hlift]

theorem selected_iff_integer_short (scale center offset : ZMod p)
    (hscale : scale ≠ 0) (a b : ℕ) (weight : ι → ℕ) (hweight : ∀ i, 1 ≤ weight i)
    (F : ZMod p → ι → ZMod p) (Fint : ι → ℤ)
    (hlift : ∀ i, (Fint i : ZMod p)=F offset i) (i₁ i₂ : ι)
    (hfirst : F offset i₁=1) (hsecond : F offset i₂=scale*(offset-center))
    (hcut₁ : p ≤ (a+1)*weight i₁) (hcut₂ : p ≤ (b+1)*weight i₂) :
    (∃ scalar : ℤ, ∃ row base : ι → ℤ, row ≠ 0 ∧ rowNorm weight row < p ∧
      ∀ i, row i=(p : ℤ)*base i+scalar*Fint i) ↔
      ∃ scalar : ZMod p, (scalar,offset) ∈ selectedPairs p scale center a b weight F := by
  constructor
  · rintro ⟨scalar,row,base,hne,hshort,hrow⟩
    exact ⟨(scalar : ZMod p),selected_complete_integer p scale center offset scalar
      hscale a b weight hweight F Fint row base hlift i₁ i₂ hfirst hsecond
      hcut₁ hcut₂ hne hrow hshort⟩
  · rintro ⟨scalar,hselected⟩
    rcases selected_sound p scale center scalar offset a b weight F hselected with
      ⟨hnonzero,hshort,_⟩
    have hF : (fun i ↦ (Fint i : ZMod p))=F offset := funext hlift
    obtain ⟨base,hbase⟩ := centered_integer_witness p scalar.valMinAbs Fint
    simp only [ZMod.coe_valMinAbs,hF] at hbase
    exact ⟨scalar.valMinAbs,centeredRow p scalar (F offset),base,
      centered_nonzero p scalar hnonzero (F offset) i₁ hfirst,hshort,hbase⟩

end CryptoLean.RankOneSelector
