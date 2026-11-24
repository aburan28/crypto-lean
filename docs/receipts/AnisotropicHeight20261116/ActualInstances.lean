import CryptoLean.Polynomial.HeightBudget
import CryptoLean.Semaev.S3
import CryptoLean.Combinatorics.ChainPowerBlocks
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open CryptoLean.BalancedFiltration CryptoLean.HeightBudget

namespace AnisotropicActual

abbrev P := MvPolynomial (Fin 8) ℤ

def projectiveWeight : (Fin 8 →₀ ℕ) →+ ℕ :=
  Finsupp.applyAddHom (4 : Fin 8) + Finsupp.applyAddHom (5 : Fin 8) +
    Finsupp.applyAddHom (6 : Fin 8) + Finsupp.applyAddHom (7 : Fin 8)

def leafDegree (m : Fin 8 →₀ ℕ) : ℕ := m 0+m 1+m 2+m 3

def slotDegree (i : Fin 2) (m : Fin 8 →₀ ℕ) : ℕ :=
  if i=0 then m 4+m 6 else m 5+m 7

def row (a b x y U V : P) : P :=
  (x-y)^2*U^2 - 2*((x+y)*(x*y+a)+2*b)*U*V +
    ((x*y-a)^2-4*b*(x+y))*V^2

def first (a b τ : ℤ) : P :=
  row (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.X 0) (MvPolynomial.X 1)
    (MvPolynomial.X 4+MvPolynomial.C τ*MvPolynomial.X 6) (MvPolynomial.X 6)

def middle (a b τ υ : ℤ) : P :=
  let A := MvPolynomial.C a
  let B := MvPolynomial.C b
  let X := MvPolynomial.X (2 : Fin 8)
  let U := MvPolynomial.X (4 : Fin 8)+MvPolynomial.C τ*MvPolynomial.X 6
  let V := MvPolynomial.X (6 : Fin 8)
  let W := MvPolynomial.X (5 : Fin 8)+MvPolynomial.C υ*MvPolynomial.X 7
  let Z := MvPolynomial.X (7 : Fin 8)
  (U-X*V)^2*W^2 - 2*((U+X*V)*(U*X+A*V)+2*B*V^2)*W*Z +
    ((U*X-A*V)^2-4*B*(U+X*V)*V)*Z^2

def last (a b q υ : ℤ) : P :=
  row (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.X 3) (MvPolynomial.C q)
    (MvPolynomial.X 5+MvPolynomial.C υ*MvPolynomial.X 7) (MvPolynomial.X 7)

theorem chain_generators_mem (p : ℕ) (a b q τ υ : ℤ) :
    ∀ g ∈ ({MvPolynomial.C (p : ℤ), first a b τ, middle a b τ υ,
      last a b q υ} : Set P), g ∈ filtrationIdeal p projectiveWeight 1 := by
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact modulus_mem p projectiveWeight
  · have h := shifted_quadratic_mem p projectiveWeight (4 : Fin 8) (6 : Fin 8)
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      ((MvPolynomial.X 0-MvPolynomial.X 1)^2)
      (-2*((MvPolynomial.X 0+MvPolynomial.X 1)*
        (MvPolynomial.X 0*MvPolynomial.X 1+MvPolynomial.C a)+2*MvPolynomial.C b))
      ((MvPolynomial.X 0*MvPolynomial.X 1-MvPolynomial.C a)^2-
        4*MvPolynomial.C b*(MvPolynomial.X 0+MvPolynomial.X 1)) (MvPolynomial.C τ)
    simpa only [first, row, sub_eq_add_neg, neg_mul, mul_assoc] using h
  · let X : P := MvPolynomial.X 2
    let U : P := MvPolynomial.X 4+MvPolynomial.C τ*MvPolynomial.X 6
    let V : P := MvPolynomial.X 6
    have h := shifted_quadratic_mem p projectiveWeight (5 : Fin 8) (7 : Fin 8)
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      ((U-X*V)^2)
      (-2*((U+X*V)*(U*X+MvPolynomial.C a*V)+2*MvPolynomial.C b*V^2))
      ((U*X-MvPolynomial.C a*V)^2-4*MvPolynomial.C b*(U+X*V)*V)
      (MvPolynomial.C υ)
    simpa only [middle, X, U, V, sub_eq_add_neg, neg_mul, mul_assoc] using h
  · have h := shifted_quadratic_mem p projectiveWeight (5 : Fin 8) (7 : Fin 8)
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      (by simp [projectiveWeight, Finsupp.applyAddHom])
      ((MvPolynomial.X 3-MvPolynomial.C q)^2)
      (-2*((MvPolynomial.X 3+MvPolynomial.C q)*
        (MvPolynomial.X 3*MvPolynomial.C q+MvPolynomial.C a)+2*MvPolynomial.C b))
      ((MvPolynomial.X 3*MvPolynomial.C q-MvPolynomial.C a)^2-
        4*MvPolynomial.C b*(MvPolynomial.X 3+MvPolynomial.C q)) (MvPolynomial.C υ)
    simpa only [last, row, sub_eq_add_neg, neg_mul, mul_assoc] using h

example (p H t B : ℕ) (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (height : Fin 2 → ℕ) (hmin : ∀ i, H ≤ height i)
    (f : P) (hf : Filtered p projectiveWeight t f)
    (hshort : coefficientNorm (fun m ↦ B^(leafDegree m) *
      ∏ i : Fin 2, (height i)^(slotDegree i m)) f < p^t)
    (hbudget : p^t ≤ B*H^(2*t))
    (m : Fin 8 →₀ ℕ) (hl : 0 < leafDegree m) : f.coeff m = 0 := by
  apply anisotropic_short_leaf_coeff_zero Finset.univ height slotDegree
    p H t B hH hp hB (fun i _ ↦ hmin i) projectiveWeight ?_ leafDegree
    f hf hshort hbudget m hl
  intro n
  change n 4+n 5+n 6+n 7 = ∑ i : Fin 2, slotDegree i n
  rw [Fin.sum_univ_two]
  change n 4+n 5+n 6+n 7 = (n 4+n 6)+(n 5+n 7)
  omega

example (p H t B : ℕ) (hH : 1 ≤ H) (hp : H^2 ≤ p) (hB : 0 < B)
    (a b q τ υ : ℤ) (f : P)
    (hf : f ∈ (Ideal.span ({MvPolynomial.C (p : ℤ), first a b τ,
      middle a b τ υ, last a b q υ} : Set P))^t)
    (W : (Fin 8 →₀ ℕ) → ℕ)
    (hW : ∀ m, B^(leafDegree m)*H^(projectiveWeight m) ≤ W m)
    (hshort : coefficientNorm W f < p^t) (hbudget : p^t ≤ B*H^(2*t))
    (m : Fin 8 →₀ ℕ) (hl : 0 < leafDegree m) : f.coeff m = 0 := by
  exact span_power_short_leaf_coeff_zero p H t B hH hp hB projectiveWeight
    leafDegree W hW _ (chain_generators_mem p a b q τ υ) f hf hshort hbudget m hl

example (p : ℕ) [Fact p.Prime] (a b x y U V τ : ZMod p) (hV : V ≠ 0) :
    V^2 * CryptoLean.Semaev.S3 a b x y (τ+U/V) =
      (x-y)^2*(U+τ*V)^2 - 2*((x+y)*(x*y+a)+2*b)*(U+τ*V)*V +
        ((x*y-a)^2-4*b*(x+y))*V^2 := by
  unfold CryptoLean.Semaev.S3
  field_simp
  ring

example {K : Type*} [Field K] (a b x y z : K) :
    CryptoLean.Semaev.S3 a b x y z = CryptoLean.Semaev.S3 a b y z x := by
  unfold CryptoLean.Semaev.S3
  ring

example (a b q τ υ : ℤ) (modulus : ℕ) (hP : 0 < modulus)
    (W : (Fin 8 →₀ ℕ) → ℕ) (hW : ∀ m, 1 ≤ W m)
    (f high low : P)
    (hhigh : high ∈ Ideal.span ({MvPolynomial.C (0 : ℤ), first a b τ,
      middle a b τ υ, last a b q υ} : Set P))
    (hlow : ∀ m, low.coeff m ≠ 0 → projectiveWeight m < 2)
    (hf : f=high+MvPolynomial.C (modulus : ℤ)*low)
    (hshort : coefficientNorm W f < modulus) :
    f ∈ Ideal.span ({MvPolynomial.C (0 : ℤ), first a b τ,
      middle a b τ υ, last a b q υ} : Set P) := by
  apply short_mem_original_ideal _ projectiveWeight ?_ modulus hP W hW f high low
    hhigh hlow hf hshort
  exact fun g hg ↦ (Ideal.span_le.mpr (chain_generators_mem 0 a b q τ υ)) hg

end AnisotropicActual

open CryptoLean.ChainPowerBlocks

example (n t : ℕ) (S : Finset (Fin (n+1) → ℕ)) (profile : Fin n → ℕ)
    (hbudget : ∀ e ∈ S, (∑ i, e i) ≤ t)
    (hprofile : ∀ e ∈ S, ∀ i, 2*adjacent n e i = profile i) : S.card ≤ t+1 := by
  apply block_card_le n t S (fun i ↦ profile i/2)
  · intro e he
    have hsum : e 0 ≤ ∑ i : Fin (n+1), e i :=
      Finset.single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ _)
    exact hsum.trans (hbudget e he)
  · intro e he
    funext i
    have h := hprofile e he i
    omega

example (n t : ℕ)
    (S : Finset ((Fin (n+1) → ℕ) × (Fin (3*n+2) → ℕ)))
    (menu : Finset (Fin (3*n+2) → ℕ)) (profile : Fin n → ℕ)
    (hmenu : ∀ r ∈ S, r.2 ∈ menu)
    (hhead : ∀ r ∈ S, r.1 0 ≤ t)
    (hprofile : ∀ r ∈ S, ∀ i : Fin n,
      2*adjacent n r.1 i + r.2 ⟨n+2+i, by omega⟩ +
        r.2 ⟨2*n+2+i, by omega⟩ = profile i) :
    S.card ≤ (t+1)*menu.card := by
  apply shifted_block_card_le n t S menu
    (fun δ i ↦ δ ⟨n+2+i, by omega⟩+δ ⟨2*n+2+i, by omega⟩)
    profile hmenu hhead
  intro r hr i
  simpa only [Nat.add_assoc] using hprofile r hr i
