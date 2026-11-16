import CryptoLean.Polynomial.ProjectiveSubresultant
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Honest six-block support and independent leaf-multiplier rows. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace CryptoLean.ResidualLeafRank
open Polynomial CryptoLean.ProjectiveSubresultant
variable {R : Type*} [CommRing R]

def alpha (τ σ w : R) : Fin 6 → R :=
  ![2,4*(σ-w),2*(σ-w)^2,2*τ,4*τ*(σ-w),2*τ*(σ-w)^2]
def beta (a b τ σ w : R) : Fin 6 → R :=
  ![-2*w,-2*(2*w*σ+a+w^2),-2*adjacentLinear a b w σ 1,
    w^2-2*τ*w,2*w^2*σ-2*(a*w+2*b)-2*τ*(2*w*σ+a+w^2),
    adjacentConstant a b w σ 1-2*τ*adjacentLinear a b w σ 1]
def gamma (σ w : R) : Fin 6 → R := ![0,0,0,-1,-2*(σ-w),-(σ-w)^2]

def core (a b x y α β γ : R) : R :=
  α*firstLinear a b x y+β*(x-y)^2+γ*firstConstant a b x y

def block (a b x y w τ σ : R) (i : Fin 6) : R :=
  core a b x y (alpha τ σ w i) (beta a b τ σ w i) (gamma σ w i)

theorem source_homogeneous_blocks (a b x y w τ σ U V T W : R) :
    CryptoLean.ProjectiveSubresultant.residual a b x y w (U+τ*V) V (T+σ*W) W =
      block a b x y w τ σ 0*U*T^2+block a b x y w τ σ 1*U*T*W+
      block a b x y w τ σ 2*U*W^2+block a b x y w τ σ 3*V*T^2+
      block a b x y w τ σ 4*V*T*W+block a b x y w τ σ 5*V*W^2 := by
  simp [block,core,alpha,beta,gamma,CryptoLean.ProjectiveSubresultant.residual,
    firstLinear,firstConstant,adjacentLinear,adjacentConstant]
  ring

theorem source_block_identity (a b x y w τ σ U T : R) :
    residual a b x y w (U+τ) 1 (T+σ) 1 =
      (block a b x y w τ σ 0*U+block a b x y w τ σ 3)*T^2+
      (block a b x y w τ σ 1*U+block a b x y w τ σ 4)*T+
      (block a b x y w τ σ 2*U+block a b x y w τ σ 5) := by
  have h := source_homogeneous_blocks a b x y w τ σ U 1 T 1
  simp only [mul_one,one_pow] at h
  linear_combination h

def coreInX (a b y α β γ : R) : Polynomial R :=
  core (C a) (C b) X (C y) (C α) (C β) (C γ)

theorem core_x_square (a b y α β γ : R) :
    (coreInX a b y α β γ).coeff 2=α*y+β+γ*y^2 := by
  let q := α*y+β+γ*y^2
  have he : coreInX a b y α β γ = C q*X^2+
      C (core a b 1 y α β γ-core a b 0 y α β γ-q)*X+C (core a b 0 y α β γ) := by
    simp only [coreInX,core,firstLinear,firstConstant,q,map_add,map_sub,map_mul,map_pow,
      map_ofNat,map_zero,map_one]
    ring
  rw [he]
  simp only [Polynomial.coeff_add,Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num [q]

def coreXY (a b α β γ : R) : Polynomial (Polynomial R) :=
  coreInX (C a) (C b) X (C α) (C β) (C γ)

theorem core_xy_coeffs (a b α β γ : R) :
    ((coreXY a b α β γ).coeff 2).coeff 1=α ∧
    ((coreXY a b α β γ).coeff 2).coeff 2=γ := by
  simp only [coreXY,core_x_square]
  norm_num [Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X]

variable {S : Type*} [CommRing S]

theorem vectors_map (f : R →+* S) (a b τ σ w : R) (i : Fin 6) :
    f (alpha τ σ w i)=alpha (f τ) (f σ) (f w) i ∧
    f (beta a b τ σ w i)=beta (f a) (f b) (f τ) (f σ) (f w) i ∧
    f (gamma σ w i)=gamma (f σ) (f w) i := by
  fin_cases i <;> simp [alpha,beta,gamma,adjacentLinear,adjacentConstant,
    map_ofNat,map_add,map_sub,map_mul,map_pow,map_neg]

theorem block_map (f : R →+* S) (a b x y w τ σ : R) (i : Fin 6) :
    f (block a b x y w τ σ i)=block (f a) (f b) (f x) (f y) (f w) (f τ) (f σ) i := by
  have h := vectors_map f a b τ σ w i
  simp only [block,core,firstLinear,firstConstant,map_add,map_sub,map_mul,map_pow,
    map_ofNat,h.1,h.2.1,h.2.2]

theorem nested_block (a b τ σ w : R) (i : Fin 6) :
    block (C (C a)) (C (C b)) X (C X) (C (C w)) (C (C τ)) (C (C σ)) i =
      coreXY a b (alpha τ σ w i) (beta a b τ σ w i) (gamma σ w i) := by
  let f : R →+* Polynomial (Polynomial R) := Polynomial.C.comp Polynomial.C
  have h := vectors_map f a b τ σ w i
  dsimp [f] at h
  unfold block
  rw [← h.1,← h.2.1,← h.2.2]
  rfl

section Support
variable {ι : Type*} {K : Type*} [Field K]

def rowSupport (A : Finset (ι →₀ ℕ)) (P : MvPolynomial ι K) : Finset (ι →₀ ℕ) := by
  classical
  exact A.biUnion (fun m ↦ (MvPolynomial.monomial m 1*P).support)

def honestSupport (A : Finset (ι →₀ ℕ)) (P : Fin 6 → MvPolynomial ι K) :
    Finset (Σ _ : Fin 6, ι →₀ ℕ) :=
  Finset.univ.sigma (fun i ↦ rowSupport A (P i))

theorem rowSupport_card_lower (A : Finset (ι →₀ ℕ)) (P : MvPolynomial ι K)
    (hP : P ≠ 0) : A.card ≤ (rowSupport A P).card := by
  classical
  obtain ⟨v,hv⟩ := MvPolynomial.exists_coeff_ne_zero hP
  have hs : A.image (fun u ↦ u+v) ⊆ rowSupport A P := by
    intro n hn
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_biUnion.mpr
    refine ⟨u,hu,MvPolynomial.mem_support_iff.mpr ?_⟩
    simpa only [MvPolynomial.coeff_monomial_mul,one_mul] using hv
  have hi : Function.Injective (fun u : ι →₀ ℕ ↦ u+v) := fun _ _ h ↦ add_right_cancel h
  calc
    A.card = (A.image (fun u ↦ u+v)).card := (Finset.card_image_of_injective A hi).symm
    _ ≤ _ := Finset.card_le_card hs

theorem honestSupport_card_lower (A : Finset (ι →₀ ℕ)) (P : Fin 6 → MvPolynomial ι K)
    (hP : ∀ i, P i ≠ 0) : 6*A.card ≤ (honestSupport A P).card := by
  classical
  calc
    6*A.card = ∑ _i : Fin 6, A.card := by simp [Nat.mul_comm]
    _ ≤ ∑ i : Fin 6, (rowSupport A (P i)).card :=
      Finset.sum_le_sum (fun i _ ↦ rowSupport_card_lower A (P i) (hP i))
    _ = (honestSupport A P).card := by simp [honestSupport,Finset.card_sigma]

/-- No linear relation between distinct leaf monomial multiplier rows. -/
theorem no_leaf_linear_relation (A : Finset (ι →₀ ℕ)) (P : Fin 6 → MvPolynomial ι K)
    (hP : P 0 ≠ 0) (c : (ι →₀ ℕ) → K)
    (hzero : ∀ i, ∑ m ∈ A, MvPolynomial.monomial m (c m)*P i=0) :
    ∀ m ∈ A, c m=0 := by
  classical
  have hz : ∑ m ∈ A, MvPolynomial.monomial m (c m)=0 := by
    have h := hzero 0
    rw [← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hP
  intro m hm
  have h := congrArg (fun f : MvPolynomial ι K ↦ f.coeff m) hz
  simpa [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hm] using h

end Support

variable {K : Type*} [Field K]

abbrev Leaf (K : Type*) [Field K] := MvPolynomial (Fin 3) K

def sourceBlocks (a b τ σ : K) : Fin 6 → Leaf K :=
  block (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.C τ) (MvPolynomial.C σ)

/-- Bind three maintained polynomial-ring constructors for the target interface. -/
local instance standardThreeRing : CommRing (Polynomial (Polynomial (Polynomial K))) :=
  @Polynomial.commRing (Polynomial (Polynomial K))
    (@Polynomial.commRing (Polynomial K) (@Polynomial.commRing K inferInstance))

def lift3Hom : K →+* Polynomial (Polynomial (Polynomial K)) :=
  (Polynomial.C : Polynomial (Polynomial K) →+* Polynomial (Polynomial (Polynomial K))).comp
    (Polynomial.C.comp Polynomial.C)

def realize : Leaf K →+* Polynomial (Polynomial (Polynomial K)) :=
  MvPolynomial.eval₂Hom lift3Hom (fun i ↦ ![X,C X,C (C X)] i)

theorem realized_source (a b τ σ : K) (i : Fin 6) :
    realize (sourceBlocks a b τ σ i) =
      coreXY (C a) (C b) (alpha (C τ) (C σ) X i)
        (beta (C a) (C b) (C τ) (C σ) X i) (gamma (C σ) X i) := by
  rw [sourceBlocks,block_map]
  have hc (z : K) : realize (MvPolynomial.C z)=C (C (C z)) := by
    simp [realize,lift3Hom]
  have hx : realize (MvPolynomial.X 0 : Leaf K)=X := by simp [realize]
  have hy : realize (MvPolynomial.X 1 : Leaf K)=C X := by simp [realize]
  have hw : realize (MvPolynomial.X 2 : Leaf K)=C (C X) := by simp [realize]
  rw [hc,hc,hx,hy,hw,hc,hc]
  exact nested_block (C a) (C b) (C τ) (C σ) X i

def yDegree : Fin 6 → ℕ := ![1,1,1,2,2,2]
def wDegree : Fin 6 → ℕ := ![0,1,2,0,1,2]
def witnessValues : Fin 6 → K := ![2,-4,2,-1,2,-1]

def coefficientWitness (P : Polynomial (Polynomial (Polynomial K))) (i : Fin 6) : K :=
  ((P.coeff 2).coeff (yDegree i)).coeff (wDegree i)

theorem source_witness_values (a b τ σ : K) (i : Fin 6) :
    coefficientWitness (realize (sourceBlocks a b τ σ i)) i=witnessValues i := by
  rw [realized_source]
  have h₁ (A B C₀ : Polynomial K) : ((coreXY (C a) (C b) A B C₀).coeff 2).coeff 1=A :=
    (core_xy_coeffs (C a) (C b) A B C₀).1
  have h₂ (A B C₀ : Polynomial K) : ((coreXY (C a) (C b) A B C₀).coeff 2).coeff 2=C₀ :=
    (core_xy_coeffs (C a) (C b) A B C₀).2
  fin_cases i <;> dsimp [coefficientWitness,yDegree,wDegree]
  all_goals first | rw [h₁] | rw [h₂]
  all_goals norm_num [witnessValues,alpha,gamma,pow_two,Polynomial.coeff_mul,
    Polynomial.coeff_X,Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero]

theorem highest_leaf_chart_anchors (a b τ σ : K) :
    (((realize (sourceBlocks a b τ σ 5)).coeff 2).coeff 2).coeff 2 = -1 ∧
    (((realize (sourceBlocks a b τ σ 5)).coeff 2).coeff 2).coeff 1 = 2*σ ∧
    (((realize (sourceBlocks a b τ σ 5)).coeff 2).coeff 1).coeff 2 = 2*τ := by
  have h := core_xy_coeffs (C a) (C b) (alpha (C τ) (C σ) X 5)
    (beta (C a) (C b) (C τ) (C σ) X 5) (gamma (C σ) X 5)
  simp only [realized_source,h.1,h.2]
  norm_num [alpha,gamma,pow_two,Polynomial.coeff_mul,Polynomial.coeff_X,
    Finset.Nat.antidiagonal_succ,Finset.Nat.antidiagonal_zero]
  ring

theorem highest_chart_decode (scalar τ σ c d : K) (hl : scalar ≠ 0) (h₂ : (2 : K) ≠ 0)
    (hc : c=2*scalar*σ) (hd : d=2*scalar*τ) :
    σ=c/(2*scalar) ∧ τ=d/(2*scalar) := by
  have hn := mul_ne_zero h₂ hl
  constructor
  · apply (eq_div_iff hn).2
    rw [hc]
    ring
  · apply (eq_div_iff hn).2
    rw [hd]
    ring

theorem witnessValues_nonzero (h₂ : (2 : K) ≠ 0) (i : Fin 6) : witnessValues (K:=K) i ≠ 0 := by
  have h₄ : (4 : K) ≠ 0 := by
    have he : (4 : K)=2*2 := by ring
    rw [he]
    exact mul_ne_zero h₂ h₂
  fin_cases i <;> simp [witnessValues,h₂,h₄]

theorem sourceBlocks_nonzero (a b τ σ : K) (h₂ : (2 : K) ≠ 0) (i : Fin 6) :
    sourceBlocks a b τ σ i ≠ 0 := by
  intro hz
  have h := source_witness_values a b τ σ i
  rw [hz,map_zero] at h
  have he : (0 : K)=witnessValues i := by simpa [coefficientWitness] using h
  exact witnessValues_nonzero h₂ i he.symm

theorem source_honest_support_lower (a b τ σ : K) (h₂ : (2 : K) ≠ 0)
    (A : Finset (Fin 3 →₀ ℕ)) :
    6*A.card ≤ (honestSupport A (sourceBlocks a b τ σ)).card :=
  honestSupport_card_lower A _ (sourceBlocks_nonzero a b τ σ h₂)

theorem source_no_linear_relation (a b τ σ : K) (h₂ : (2 : K) ≠ 0)
    (A : Finset (Fin 3 →₀ ℕ)) (c : (Fin 3 →₀ ℕ) → K)
    (hz : ∀ i, ∑ m ∈ A, MvPolynomial.monomial m (c m)*sourceBlocks a b τ σ i=0) :
    ∀ m ∈ A, c m=0 :=
  no_leaf_linear_relation A _ (sourceBlocks_nonzero a b τ σ h₂ 0) c hz

theorem six_block_codimension (N r : ℕ) (hN : 6*r ≤ N) : 5*N ≤ 6*(N-r) := by omega

theorem volume_charge (p L N r : ℕ) (hL : 1 ≤ L) (hN : 6*r ≤ N) (hcap : p ≤ L^6) :
    p^N ≤ L^N*p^(N-r) := by
  have hr : r ≤ N := by omega
  have hpow : p^r ≤ L^N := by
    calc
      _ ≤ (L^6)^r := Nat.pow_le_pow_left hcap r
      _ = L^(6*r) := by rw [pow_mul]
      _ ≤ _ := Nat.pow_le_pow_right hL hN
  calc
    p^N = p^r*p^(N-r) := by rw [← pow_add]; congr 1; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hpow

theorem short_volume_forces_height (p L N r : ℕ) (hL : 1 ≤ L) (hN : 6*r ≤ N)
    (hvol : L^N*p^(N-r) < p^N) : L^6 < p := by
  by_contra hn
  have hc : p ≤ L^6 := by omega
  exact (Nat.not_lt_of_ge (volume_charge p L N r hL hN hc)) hvol

end CryptoLean.ResidualLeafRank
