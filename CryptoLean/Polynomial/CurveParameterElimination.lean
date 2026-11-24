import CryptoLean.Semaev.S3
import CryptoLean.Polynomial.EndpointCoefficients
import CryptoLean.Polynomial.HeightBudget

/-! Distinct-generator parameter cancellation and its ordinary height test.
No ECDLP yield, root-isolation or new execution claim. -/
set_option autoImplicit false
noncomputable section

namespace CryptoLean.CurveParameterElimination
variable {R : Type*} [CommRing R]

def cleared (a b A B C D : R) : R := (B-a*D)^2-4*A*(C+b*D)

theorem b_free_identity (a b A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : R) :
    A₂*D₂*cleared a b A₁ B₁ C₁ D₁-A₁*D₁*cleared a b A₂ B₂ C₂ D₂ =
      A₂*D₂*(B₁-a*D₁)^2-A₁*D₁*(B₂-a*D₂)^2-
        4*A₁*A₂*(D₂*C₁-D₁*C₂) := by
  unfold cleared
  ring

theorem shared_denominator_factor (A₁ A₂ V W F₁ F₂ : R) :
    (A₂*(V*W))*F₁-(A₁*V)*F₂ = V*(A₂*W*F₁-A₁*F₂) := by ring

theorem primitive_b_free (a b A₁ B₁ C₁ A₂ B₂ C₂ V W : R) :
    A₂*W*cleared a b A₁ B₁ C₁ V-A₁*cleared a b A₂ B₂ C₂ (V*W) =
      A₂*W*(B₁-a*V)^2-A₁*(B₂-a*V*W)^2-
        4*A₁*A₂*(W*C₁-C₂) := by
  unfold cleared
  ring

def first (a b x y Z V : R) : R :=
  (x-y)^2*Z^2-2*((x+y)*(x*y+a)+2*b)*Z*V+
    ((x*y-a)^2-4*b*(x+y))*V^2

def adjacent (a b w Z V T W : R) : R :=
  (Z-w*V)^2*T^2-2*((Z+w*V)*(Z*w+a*V)+2*b*V^2)*T*W+
    ((Z*w-a*V)^2-4*b*(Z+w*V)*V)*W^2

def firstSum (x y Z V : R) : R := Z+(x+y)*V
def adjacentSum (w Z V T W : R) : R := Z*W+w*V*W+T*V

theorem first_symmetric (a b x y Z V : R) :
    cleared a b (firstSum x y Z V) (x*y*V+(x+y)*Z) (x*y*Z) V =
      first a b x y Z V := by
  unfold cleared firstSum first
  ring

theorem adjacent_symmetric (a b w Z V T W : R) :
    cleared a b (adjacentSum w Z V T W)
      (Z*w*W+Z*T+w*T*V) (Z*w*T) (V*W) = adjacent a b w Z V T W := by
  unfold cleared adjacentSum adjacent
  ring

def primitive (a b x y w Z V T W : R) : R :=
  adjacentSum w Z V T W*W*first a b x y Z V-
    firstSum x y Z V*adjacent a b w Z V T W

theorem primitive_independent_b (a b x y w Z V T W : R) :
    primitive a b x y w Z V T W = primitive a 0 x y w Z V T W := by
  unfold primitive adjacentSum firstSum first adjacent
  ring

theorem original_roots_primitive_zero (a b x y w Z V T W : R)
    (h₁ : first a b x y Z V = 0) (h₂ : adjacent a b w Z V T W = 0) :
    primitive a b x y w Z V T W = 0 := by
  simp [primitive,h₁,h₂]

theorem primitive_v_zero (a b x y w Z T W : R) :
    primitive a b x y w Z 0 T W =
      Z^3*((x-y)^2*W^2-(T-w*W)^2) := by
  unfold primitive adjacentSum firstSum first adjacent
  ring

theorem primitive_w_zero (a b x y w Z V T : R) :
    primitive a b x y w Z V T 0 =
      -(Z+(x+y)*V)*(Z-w*V)^2*T^2 := by
  unfold primitive adjacentSum firstSum first adjacent
  ring

theorem primitive_scaling (a b x y w Z V T W r s : R) :
    primitive a b x y w (r*Z) (r*V) (s*T) (s*W) =
      r^3*s^2*primitive a b x y w Z V T W := by
  unfold primitive adjacentSum firstSum first adjacent
  ring

variable {K : Type*} [Field K]

theorem symmetric_s3 (a b x y z : K) :
    CryptoLean.Semaev.S3 a b x y z =
      cleared a b (x+y+z) (x*y+x*z+y*z) (x*y*z) 1 := by
  unfold CryptoLean.Semaev.S3 cleared
  ring

theorem first_clears_s3 (a b x y Z V : K) (hV : V ≠ 0) :
    first a b x y Z V = V^2*CryptoLean.Semaev.S3 a b x y (Z/V) := by
  unfold first CryptoLean.Semaev.S3
  field_simp

theorem adjacent_clears_s3 (a b w Z V T W : K) (hV : V ≠ 0) (hW : W ≠ 0) :
    adjacent a b w Z V T W = V^2*W^2*CryptoLean.Semaev.S3 a b (Z/V) w (T/W) := by
  unfold adjacent CryptoLean.Semaev.S3
  field_simp

theorem retained_equation_equiv (Z₁ Z₂ F₁ F₂ : K) (hZ : Z₁ ≠ 0) :
    (F₁=0 ∧ Z₂*F₁-Z₁*F₂=0) ↔ (F₁=0 ∧ F₂=0) := by
  constructor
  · rintro ⟨h₁,hg⟩
    have hz : Z₁*F₂=0 := by simpa [h₁] using hg
    exact ⟨h₁,(mul_eq_zero.mp hz).resolve_left hZ⟩
  · rintro ⟨h₁,h₂⟩
    simp [h₁,h₂]

theorem retained_with_zero_branch (Z₁ Z₂ F₁ F₂ : K) :
    (F₁=0 ∧ F₂=0) ↔
      (Z₁≠0 ∧ F₁=0 ∧ Z₂*F₁-Z₁*F₂=0) ∨ (Z₁=0 ∧ F₁=0 ∧ F₂=0) := by
  by_cases hZ : Z₁=0
  · simp [hZ]
  · simpa [hZ] using (retained_equation_equiv Z₁ Z₂ F₁ F₂ hZ).symm

theorem profile_product_lower (H₁ H₂ : ℕ) (hH : 1 ≤ H₁) :
    H₁^2*H₂^2 ≤ H₁^3*H₂^2 :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 3))

theorem profile_short_product (H₁ H₂ N p : ℕ) (hH : 1 ≤ H₁)
    (hN : H₁^3*H₂^2 ≤ N) (hshort : N < p) : H₁^2*H₂^2 < p :=
  (profile_product_lower H₁ H₂ hH).trans_lt (hN.trans_lt hshort)

theorem coverage_charge (p Q K : ℕ) (hp : 0 < p)
    (hK : K < p) (hcover : p^2 ≤ 9*Q*K) : p < 9*Q := by
  by_contra hn
  have hQ : 9*Q ≤ p := by omega
  have hu := Nat.mul_le_mul_right K hQ
  have hs := Nat.mul_lt_mul_of_pos_left hK hp
  nlinarith

theorem cover_union_card {H : Type*} [Fintype H] [DecidableEq H]
    (Q M : ℕ) (A : Fin Q → Finset H)
    (hcover : ∀ x, ∃ j, x ∈ A j) (hcard : ∀ j, (A j).card ≤ M) :
    Fintype.card H ≤ Q*M := by
  have hs : (Finset.univ : Finset H) ⊆ Finset.univ.biUnion A := by
    intro x _
    obtain ⟨j,hj⟩ := hcover x
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hj⟩
  calc
    _ = (Finset.univ : Finset H).card := by simp
    _ ≤ (Finset.univ.biUnion A).card := Finset.card_le_card hs
    _ ≤ ∑ j ∈ Finset.univ, (A j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin Q, M := Finset.sum_le_sum (fun j _ ↦ hcard j)
    _ = _ := by simp

theorem nonzero_norm_min_weight {σ : Type*} (M : ℕ)
    (W : (σ →₀ ℕ) → ℕ) (f : MvPolynomial σ ℤ) (hf : f ≠ 0)
    (hW : ∀ m ∈ f.support, M ≤ W m) : M ≤ CryptoLean.HeightBudget.coefficientNorm W f := by
  obtain ⟨m,hm⟩ : ∃ m, f.coeff m ≠ 0 := by
    by_contra! h
    apply hf
    ext m
    simp [h m]
  have hc : 1 ≤ (f.coeff m).natAbs := Int.natAbs_pos.mpr hm
  calc
    M ≤ W m := hW m (MvPolynomial.mem_support_iff.mpr hm)
    _ = 1*W m := by simp
    _ ≤ (f.coeff m).natAbs*W m := Nat.mul_le_mul_right _ hc
    _ ≤ _ := CryptoLean.HeightBudget.coefficient_le_norm W f m hm

end CryptoLean.CurveParameterElimination
