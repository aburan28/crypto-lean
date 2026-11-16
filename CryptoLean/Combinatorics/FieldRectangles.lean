import CryptoLean.Combinatorics.UniversalPools
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Finite-field offset bounds from two coefficient windows.
The normalization/fraction interpretation is separate from these cardinal laws. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.FieldRectangles

variable {K : Type*} [Field K] [DecidableEq K]

def rectangleImage (scale center : K) (A B : Finset K) : Finset K :=
  ((A.erase 0) ×ˢ B).image (fun ab ↦ center+(scale*ab.1)⁻¹*ab.2)

theorem mem_rectangleImage (scale center offset : K) (hscale : scale ≠ 0)
    (A B : Finset K) :
    offset ∈ rectangleImage scale center A B ↔
      ∃ a ∈ A, a ≠ 0 ∧ ∃ b ∈ B, b=scale*a*(offset-center) := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp h
    rcases Finset.mem_product.mp hab with ⟨ha,hb⟩
    have ha0 := (Finset.mem_erase.mp ha).1
    refine ⟨a,(Finset.mem_erase.mp ha).2,ha0,b,hb,?_⟩
    simp [mul_assoc, hscale, ha0]
  · rintro ⟨a,ha,ha0,b,hb,heq⟩
    refine Finset.mem_image.mpr ⟨(a,b),
      Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨ha0,ha⟩,hb⟩,?_⟩
    dsimp
    rw [heq]
    simp [mul_assoc, hscale, ha0]

theorem rectangleImage_card_le (scale center : K) (A B : Finset K) :
    (rectangleImage scale center A B).card ≤ A.card*B.card := by
  calc
    _ ≤ ((A.erase 0) ×ˢ B).card := Finset.card_image_le
    _ = (A.erase 0).card*B.card := Finset.card_product _ _
    _ ≤ _ := Nat.mul_le_mul_right _
      (Finset.card_le_card (Finset.erase_subset 0 A))

def intWindow (K : Type*) [Field K] [DecidableEq K] (n : ℕ) : Finset K :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).image (fun z : ℤ ↦ (z : K))

theorem intWindow_card_le (n : ℕ) : (intWindow K n).card ≤ 2*n+1 := by
  calc
    _ ≤ (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := Finset.card_image_le
    _ = _ := by rw [Int.card_Icc]; omega

theorem mem_intWindow_of_bounds (n : ℕ) (z : ℤ)
    (hz : -(n : ℤ) ≤ z ∧ z ≤ n) : (z : K) ∈ intWindow K n := by
  exact Finset.mem_image.mpr ⟨z,Finset.mem_Icc.mpr hz,rfl⟩

theorem integer_rectangle_card_le (scale center : K) (a b : ℕ) :
    (rectangleImage scale center (intWindow K a) (intWindow K b)).card ≤
      (2*a+1)*(2*b+1) := by
  exact (rectangleImage_card_le scale center _ _).trans
    (Nat.mul_le_mul (intWindow_card_le a) (intWindow_card_le b))

theorem from_integer_coefficients (scale center offset scalar : K)
    (hscale : scale ≠ 0) (hscalar : scalar ≠ 0)
    (a b : ℕ) (c d : ℤ)
    (hc : -(a : ℤ) ≤ c ∧ c ≤ a) (hd : -(b : ℤ) ≤ d ∧ d ≤ b)
    (hfirst : (c : K)=scalar) (hsecond : (d : K)=scale*scalar*(offset-center)) :
    offset ∈ rectangleImage scale center (intWindow K a) (intWindow K b) := by
  apply (mem_rectangleImage scale center offset hscale _ _).mpr
  refine ⟨(c : K),mem_intWindow_of_bounds a c hc,?_,(d : K),
    mem_intWindow_of_bounds b d hd,?_⟩
  · simpa only [hfirst] using hscalar
  · simpa only [hfirst] using hsecond

variable [Fintype K]

theorem rectangle_miss_count_lower (Q : ℕ) (scale center : K) (A B : Finset K) :
    (Fintype.card K-A.card*B.card)^Q ≤
      (CryptoLean.UniversalPools.missPools Q (rectangleImage scale center A B)).card := by
  rw [CryptoLean.UniversalPools.fixed_miss_count]
  exact Nat.pow_le_pow_left
    (Nat.sub_le_sub_left (rectangleImage_card_le scale center A B) _) Q

theorem integer_rectangle_miss_count_lower (Q a b : ℕ) (scale center : K) :
    (Fintype.card K-(2*a+1)*(2*b+1))^Q ≤
      (CryptoLean.UniversalPools.missPools Q
        (rectangleImage scale center (intWindow K a) (intWindow K b))).card := by
  rw [CryptoLean.UniversalPools.fixed_miss_count]
  exact Nat.pow_le_pow_left
    (Nat.sub_le_sub_left (integer_rectangle_card_le scale center a b) _) Q

end CryptoLean.FieldRectangles
