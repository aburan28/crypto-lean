import CryptoLean.Polynomial.TwoChartCoefficients
import CryptoLean.Polynomial.ShortCoefficientWindows

/-! Exact small-lift rigidity under explicit strict coefficient bounds.
No unconditional selector-yield or ECDLP impossibility statement. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.SmallLiftRigidity

theorem small_divisible_zero (p : ℕ) (z : ℤ)
    (hdiv : (p : ℤ) ∣ z) (hsmall : z.natAbs < p) : z=0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv (by simpa using hsmall)

theorem cross_abs_bound (c d f g : ℤ) :
    (c*g-d*f).natAbs ≤ c.natAbs*g.natAbs+d.natAbs*f.natAbs := by
  simpa only [Int.natAbs_mul] using Int.natAbs_sub_le (c*g) (d*f)

theorem cross_exact (p : ℕ) (c d f g : ℤ)
    (hdiv : (p : ℤ) ∣ c*g-d*f)
    (hsmall : c.natAbs*g.natAbs+d.natAbs*f.natAbs < p) : c*g=d*f := by
  exact sub_eq_zero.mp (small_divisible_zero p _ hdiv
    ((cross_abs_bound c d f g).trans_lt hsmall))

theorem same_row_cross_divisible (p : ℕ) (c d F A B f g : ℤ)
    (hf : f=(p : ℤ)*A+c*F) (hg : g=(p : ℤ)*B+d*F) :
    (p : ℤ) ∣ c*g-d*f := by
  refine ⟨c*B-d*A,?_⟩
  rw [hf,hg]
  ring

theorem uniform_cross_exact {ι : Type*} (p T U : ℕ) (c d : ℤ)
    (f g : ι → ℤ) (hf : ∀ i, (f i).natAbs ≤ T) (hg : ∀ i, (g i).natAbs ≤ U)
    (hdiv : ∀ i, (p : ℤ) ∣ c*g i-d*f i)
    (hsmall : c.natAbs*U+d.natAbs*T < p) : ∀ i, c*g i=d*f i := by
  intro i
  apply cross_exact p c d (f i) (g i) (hdiv i)
  exact (Nat.add_le_add (Nat.mul_le_mul_left _ (hg i))
    (Nat.mul_le_mul_left _ (hf i))).trans_lt hsmall

theorem polynomial_cross_exact {σ : Type*} (p : ℕ) (c d : ℤ)
    (f g : MvPolynomial σ ℤ)
    (hdiv : ∀ m, (p : ℤ) ∣ c*g.coeff m-d*f.coeff m)
    (hsmall : ∀ m, c.natAbs*(g.coeff m).natAbs+d.natAbs*(f.coeff m).natAbs < p) :
    MvPolynomial.C c*g=MvPolynomial.C d*f := by
  ext m
  simp only [MvPolynomial.coeff_C_mul]
  exact cross_exact p c d _ _ (hdiv m) (hsmall m)

theorem same_row_polynomials_exact {σ : Type*} (p : ℕ) (c d : ℤ)
    (F A B f g : MvPolynomial σ ℤ)
    (hf : f=MvPolynomial.C (p : ℤ)*A+MvPolynomial.C c*F)
    (hg : g=MvPolynomial.C (p : ℤ)*B+MvPolynomial.C d*F)
    (hsmall : ∀ m, c.natAbs*(g.coeff m).natAbs+d.natAbs*(f.coeff m).natAbs < p) :
    MvPolynomial.C c*g=MvPolynomial.C d*f := by
  apply polynomial_cross_exact p c d f g ?_ hsmall
  intro m
  apply same_row_cross_divisible p c d (F.coeff m) (A.coeff m) (B.coeff m)
  · rw [hf]
    simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,MvPolynomial.coeff_C_mul]
  · rw [hg]
    simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,MvPolynomial.coeff_C_mul]

theorem linear_clear_bound (B H : ℕ) (δ c x y U V : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hU : U.natAbs ≤ H) (hV : V.natAbs ≤ H) :
    (δ*U+(δ*(x+y)-c)*V).natAbs ≤ (δ.natAbs*(1+2*B)+c.natAbs)*H := by
  have hxy : (x+y).natAbs ≤ 2*B :=
    (Int.natAbs_add_le x y).trans (by omega)
  have hc : (δ*(x+y)-c).natAbs ≤ δ.natAbs*(2*B)+c.natAbs := by
    calc
      _ ≤ (δ*(x+y)).natAbs+c.natAbs := Int.natAbs_sub_le _ _
      _ = δ.natAbs*(x+y).natAbs+c.natAbs := by rw [Int.natAbs_mul]
      _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hxy) _
  calc
    _ ≤ δ.natAbs*U.natAbs+(δ*(x+y)-c).natAbs*V.natAbs := by
      simpa only [Int.natAbs_mul] using Int.natAbs_add_le (δ*U) ((δ*(x+y)-c)*V)
    _ ≤ δ.natAbs*H+(δ.natAbs*(2*B)+c.natAbs)*H :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hU) (Nat.mul_le_mul hc hV)
    _ = _ := by ring

theorem exceptional_linear_exact (p B H : ℕ) (δ c x y U V : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hU : U.natAbs ≤ H) (hV : V.natAbs ≤ H)
    (hdiv : (p : ℤ) ∣ δ*U+(δ*(x+y)-c)*V)
    (hsmall : (δ.natAbs*(1+2*B)+c.natAbs)*H < p) :
    δ*U+(δ*(x+y)-c)*V=0 :=
  small_divisible_zero p _ hdiv ((linear_clear_bound B H δ c x y U V hx hy hU hV).trans_lt hsmall)

theorem conic_abs_bound (B : ℕ) (a x y : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B) :
    (a+x^2+x*y+y^2).natAbs ≤ a.natAbs+3*B^2 := by
  have hx₂ : (x^2).natAbs ≤ B^2 := by
    simpa only [Int.natAbs_pow] using Nat.pow_le_pow_left hx 2
  have hy₂ : (y^2).natAbs ≤ B^2 := by
    simpa only [Int.natAbs_pow] using Nat.pow_le_pow_left hy 2
  have hxy : (x*y).natAbs ≤ B^2 := by
    simpa only [Int.natAbs_mul,pow_two] using Nat.mul_le_mul hx hy
  calc
    _ ≤ (a+x^2+x*y).natAbs+(y^2).natAbs := Int.natAbs_add_le _ _
    _ ≤ ((a+x^2).natAbs+(x*y).natAbs)+(y^2).natAbs :=
      Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ ≤ ((a.natAbs+(x^2).natAbs)+(x*y).natAbs)+(y^2).natAbs :=
      Nat.add_le_add_right (Nat.add_le_add_right (Int.natAbs_add_le _ _) _) _
    _ ≤ _ := by omega

theorem centered_conic_exact (p B : ℕ) (a x y : ℤ)
    (ha : a.natAbs ≤ p/2) (hB : 6*B^2 < p)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hdiv : (p : ℤ) ∣ a+x^2+x*y+y^2) : a=-(x^2+x*y+y^2) := by
  have hsmall : a.natAbs+3*B^2 < p := by omega
  have hz := small_divisible_zero p _ hdiv ((conic_abs_bound B a x y hx hy).trans_lt hsmall)
  linear_combination hz

theorem centered_conic_height (p B : ℕ) (a x y : ℤ)
    (ha : a.natAbs ≤ p/2) (hB : 6*B^2 < p)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B)
    (hdiv : (p : ℤ) ∣ a+x^2+x*y+y^2) : a.natAbs ≤ 3*B^2 := by
  rw [centered_conic_exact p B a x y ha hB hx hy hdiv,Int.natAbs_neg]
  simpa only [zero_add,Int.natAbs_zero] using conic_abs_bound B 0 x y hx hy

/-- Equality at the modulus boundary cannot replace the strict bound. -/
theorem modulus_boundary (p : ℕ) (hp : 0 < p) :
    (p : ℤ) ∣ (p : ℤ) ∧ (p : ℤ).natAbs=p ∧ (p : ℤ) ≠ 0 := by
  exact ⟨dvd_refl _,by simp,by exact_mod_cast (Nat.ne_of_gt hp)⟩

section Primitive
open CryptoLean.CurveParameterElimination
variable {R : Type*} [CommRing R]

def clearedPrimitive (a x y w δ c d U V X W : R) : R :=
  primitive a 0 x y w (δ*U-c*V) (δ*V) (δ*X+(2*d+c)*W) (δ*W)

theorem cleared_scaling (a x y w δ c d U V X W τ σ : R)
    (hτ : δ*τ = -c) (hσ : δ*σ=2*d+c) :
    clearedPrimitive a x y w δ c d U V X W =
      δ^5*primitive a 0 x y w (U+τ*V) V (X+σ*W) W := by
  have hZ : δ*U-c*V=δ*(U+τ*V) := by
    calc
      _ = δ*U+(δ*τ)*V := by rw [hτ]; ring
      _ = _ := by ring
  have hT : δ*X+(2*d+c)*W=δ*(X+σ*W) := by
    calc
      _ = δ*X+(δ*σ)*W := by rw [hσ]
      _ = _ := by ring
  rw [clearedPrimitive,hZ,hT,primitive_scaling]
  ring

theorem cleared_exceptional_zero (a x y w δ c d U V X W : R)
    (ha : a=-(x^2+x*y+y^2)) (hlinear : δ*U+(δ*(x+y)-c)*V=0) :
    clearedPrimitive a x y w δ c d U V X W=0 := by
  have hZ : δ*U-c*V=-(x+y)*(δ*V) := by linear_combination hlinear
  rw [clearedPrimitive,hZ,ha]
  exact CryptoLean.TwoChartCoefficients.exceptional_raw_zero 0 x y w (δ*V)
    (δ*X+(2*d+c)*W) (δ*W)

theorem zero_of_scaled_reference [IsDomain R] (δ scalar f g : R)
    (hδ : δ ≠ 0) (hcross : δ^5*f=scalar*g) (hg : g=0) : f=0 := by
  rw [hg,mul_zero] at hcross
  exact (mul_eq_zero.mp hcross).resolve_left (pow_ne_zero 5 hδ)

end Primitive

/-- Variables are x,y,w,U,V,X,W, including both projective denominators. -/
def clearedModel (a δ c d : ℤ) : MvPolynomial (Fin 7) ℤ :=
  clearedPrimitive (MvPolynomial.C a) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.C δ) (MvPolynomial.C c) (MvPolynomial.C d)
    (MvPolynomial.X 3) (MvPolynomial.X 4) (MvPolynomial.X 5) (MvPolynomial.X 6)

theorem clearedModel_eval (a δ c d : ℤ) (v : Fin 7 → ℤ) :
    MvPolynomial.eval v (clearedModel a δ c d) =
      clearedPrimitive a (v 0) (v 1) (v 2) δ c d (v 3) (v 4) (v 5) (v 6) := by
  simp [clearedModel,clearedPrimitive,CryptoLean.CurveParameterElimination.primitive,
    CryptoLean.CurveParameterElimination.first,CryptoLean.CurveParameterElimination.adjacent,
    CryptoLean.CurveParameterElimination.firstSum,CryptoLean.CurveParameterElimination.adjacentSum]

/-- Complete conditional composition: coefficient rigidity and bounded branch
congruences force the actual seven-variable integer lift to vanish. -/
theorem bounded_exceptional_row_zero (p B H : ℕ) (a δ c d scalar : ℤ)
    (f : MvPolynomial (Fin 7) ℤ) (v : Fin 7 → ℤ)
    (hδ : δ ≠ 0) (ha : a.natAbs ≤ p/2) (hB : 6*B^2 < p)
    (hx : (v 0).natAbs ≤ B) (hy : (v 1).natAbs ≤ B)
    (hU : (v 3).natAbs ≤ H) (hV : (v 4).natAbs ≤ H)
    (hconic : (p : ℤ) ∣ a+(v 0)^2+v 0*v 1+(v 1)^2)
    (hlinear : (p : ℤ) ∣ δ*v 3+(δ*(v 0+v 1)-c)*v 4)
    (hlinearSmall : (δ.natAbs*(1+2*B)+c.natAbs)*H < p)
    (hcross : ∀ m, (p : ℤ) ∣ scalar*(clearedModel a δ c d).coeff m-δ^5*f.coeff m)
    (hcrossSmall : ∀ m, scalar.natAbs*((clearedModel a δ c d).coeff m).natAbs+
      (δ^5).natAbs*(f.coeff m).natAbs < p) : MvPolynomial.eval v f=0 := by
  have hc := polynomial_cross_exact p scalar (δ^5) f (clearedModel a δ c d)
    hcross hcrossSmall
  have he := congrArg (MvPolynomial.eval v) hc
  simp only [map_mul,MvPolynomial.eval_C] at he
  apply zero_of_scaled_reference δ scalar (MvPolynomial.eval v f)
    (MvPolynomial.eval v (clearedModel a δ c d)) hδ he.symm
  rw [clearedModel_eval]
  exact cleared_exceptional_zero _ _ _ _ _ _ _ _ _ _ _
    (centered_conic_exact p B a (v 0) (v 1) ha hB hx hy hconic)
    (exceptional_linear_exact p B H δ c (v 0) (v 1) (v 3) (v 4)
      hx hy hU hV hlinear hlinearSmall)
end CryptoLean.SmallLiftRigidity
