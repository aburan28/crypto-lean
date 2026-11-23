import CryptoLean.Semaev.Projective.ChartSystem
import CryptoLean.Secp256k1.SemaevThree

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/SemaevLeftFoldAffine.lean at 0a47cd62f43d (PR #347).
/-!
# The Semaev 2004 affine left-fold representative

This file independently transcribes the displayed third summation polynomial
from Semaev 2004 and the fixed split `k = 1` resultant recurrence.  The
resulting `C R 14` is one coefficient-normalized representative of `f17`:
the normalization is the literal fixed-degree resultant normalization, with
coefficient unit exactly `1` at every bridge below.

The name deliberately says *Semaev 2004 left fold*.  No claim is made that
this is a unique normalization, or that another source prints these exact
coefficients.  The recursion remains a symbolic DAG; this module never
expands `C R 14`.
-/

namespace CryptoLean.Semaev.LeftFoldAffine

open Polynomial

/-- Affine variables for the source-derived left-fold representative. -/
inductive Var
  | leaf (i : ℕ)
  | output
  deriving DecidableEq

/-- Semaev 2004's displayed third summation polynomial for the short
Weierstrass equation `y² = x³ + a*x + b`.  It is repeated literally here so
the left-fold family is definitionally independent of the frozen projective
family. -/
def f3 {R : Type*} [CommRing R]
    (a b x₁ x₂ x₃ : R) : R :=
  (x₁ - x₂) ^ 2 * x₃ ^ 2
    - 2 * ((x₁ + x₂) * (x₁ * x₂ + a) + 2 * b) * x₃
    + ((x₁ * x₂ - a) ^ 2 - 4 * b * (x₁ + x₂))

/-- The local transcription is exactly the repository's already verified
Semaev `S₃` formula. -/
theorem f3_eq_S₃
    {R : Type*} [CommRing R] (a b x₁ x₂ x₃ : R) :
    f3 a b x₁ x₂ x₃ = CryptoLean.Secp256k1.Semaev.S₃ a b x₁ x₂ x₃ := by
  rfl

/-- Regard the output of an affine multivariate polynomial as the eliminated
univariate variable while retaining every leaf as a coefficient variable. -/
noncomputable def outputSlice
    {R : Type*} [CommRing R] (p : MvPolynomial Var R) :
    Polynomial (MvPolynomial Var R) :=
  MvPolynomial.eval₂Hom
    (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial Var R))
    (fun
      | .leaf i => Polynomial.C (MvPolynomial.X (.leaf i))
      | .output => Polynomial.X)
    p

/-- The local Semaev-2004 `k = 1` operand `f3(X_i, Y, T)` for secp256k1,
written in the source recurrence's argument order. -/
noncomputable def localSlice
    {R : Type*} [CommRing R] (i : ℕ) :
    Polynomial (MvPolynomial Var R) :=
  f3 0 7
    (Polynomial.C (MvPolynomial.X (.leaf i)))
    (Polynomial.C (MvPolynomial.X .output))
    Polynomial.X

/-- Full symmetry identifies source argument order with the eliminated-variable
order used by the repository's frozen local operand. -/
theorem localSlice_eq_eliminationOrder
    {R : Type*} [CommRing R] (i : ℕ) :
    localSlice (R := R) i =
      f3 (R := Polynomial (MvPolynomial Var R)) 0 7
        Polynomial.X
        (Polynomial.C (MvPolynomial.X (Var.leaf i)))
        (Polynomial.C (MvPolynomial.X Var.output)) := by
  simp [localSlice, f3]
  ring

/-- The Semaev-2004 `k = 1` left-fold representative.

`C R s` represents `f_(s+3)`, so `C R 14` represents `f17`.  The formal
resultant degrees are retained even after specializations that lower actual
degree. -/
noncomputable def C (R : Type*) [CommRing R] :
    ℕ → MvPolynomial Var R
  | 0 =>
      f3 0 7
        (MvPolynomial.X (.leaf 0))
        (MvPolynomial.X (.leaf 1))
        (MvPolynomial.X .output)
  | s + 1 =>
      Polynomial.resultant
        (outputSlice (C R s))
        (localSlice (s + 2))
        (2 ^ (s + 1)) 2

/-- Extend sixteen external affine values to the total natural-number leaf
assignment used by the symbolic family.  Leaves outside `0, ..., 15` are
irrelevant to `C R 14` and are assigned zero. -/
def externalValue
    {K : Type*} [Zero K] (x : Fin 16 → K) (i : ℕ) : K :=
  if hi : i < 16 then x ⟨i, hi⟩ else 0

/-- Affine assignment of the sixteen source variables and fixed target. -/
def assignment
    {K : Type*} [Zero K] (x : Fin 16 → K) (X : K) : Var → K
  | .leaf i => externalValue x i
  | .output => X

/-- The target-specialized Semaev-2004 left-fold `f17` representative. -/
noncomputable def S17At
    {K : Type*} [CommRing K] (x : Fin 16 → K) (X : K) : K :=
  MvPolynomial.eval (assignment x X) (C K 14)

/-! ## Exact coefficient-unit-one bridge to the repository frozen family -/

/-- Set every projective denominator coordinate to one, retaining numerator
coordinates as the corresponding affine variables. -/
noncomputable def dehom
    {R : Type*} [CommRing R] :
    MvPolynomial CryptoLean.Semaev.FrozenProjective.Var R →+*
      MvPolynomial Var R :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : R →+* MvPolynomial Var R)
    (fun
      | .leaf i .u => MvPolynomial.X (.leaf i)
      | .leaf _ .v => 1
      | .output .u => MvPolynomial.X .output
      | .output .v => 1)

@[simp] theorem dehom_X
    {R : Type*} [CommRing R]
    (v : CryptoLean.Semaev.FrozenProjective.Var) :
    dehom (R := R) (MvPolynomial.X v) =
      match v with
      | .leaf i .u => MvPolynomial.X (.leaf i)
      | .leaf _ .v => 1
      | .output .u => MvPolynomial.X .output
      | .output .v => 1 := by
  cases v with
  | leaf i a => cases a <;> simp [dehom]
  | output a => cases a <;> simp [dehom]

@[simp] theorem dehom_C
    {R : Type*} [CommRing R] (r : R) :
    dehom (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [dehom]

/-- The frozen triquadratic dehomogenizes to the independently transcribed
Semaev-2004 `f3` formula. -/
theorem HValue_affine_eq_f3
    {R : Type*} [CommRing R] [Nontrivial R]
    (x₁ x₂ x₃ : R) :
    CryptoLean.Semaev.FrozenProjective.HValue
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₁).coord
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₂).coord
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₃).coord =
      f3 0 7 x₁ x₂ x₃ := by
  simp [CryptoLean.Semaev.FrozenProjective.HValue, f3,
    CryptoLean.Semaev.FrozenProjective.ProjectivePair.coord,
    CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine]
  ring

/-- Compatibility spelling against the repository's verified `S₃`. -/
theorem HValue_affine_eq_S₃
    {R : Type*} [CommRing R] [Nontrivial R]
    (x₁ x₂ x₃ : R) :
    CryptoLean.Semaev.FrozenProjective.HValue
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₁).coord
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₂).coord
        (CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine x₃).coord =
      CryptoLean.Secp256k1.Semaev.S₃ 0 7 x₁ x₂ x₃ := by
  rw [HValue_affine_eq_f3, f3_eq_S₃]

/-- Dehomogenization commutes with selecting the eliminated output slice. -/
theorem map_outputSlice_dehom
    {R : Type*} [CommRing R]
    (p : MvPolynomial CryptoLean.Semaev.FrozenProjective.Var R) :
    (CryptoLean.Semaev.FrozenProjective.outputSlice p).map dehom =
      outputSlice (dehom p) := by
  change
    ((Polynomial.mapRingHom dehom).comp
      (MvPolynomial.eval₂Hom
        (Polynomial.C.comp
          (MvPolynomial.C : R →+*
            MvPolynomial CryptoLean.Semaev.FrozenProjective.Var R))
        (fun
          | .leaf i a =>
              Polynomial.C (MvPolynomial.X (.leaf i a))
          | .output .u => Polynomial.X
          | .output .v => 1))) p =
      ((MvPolynomial.eval₂Hom
        (Polynomial.C.comp (MvPolynomial.C : R →+* MvPolynomial Var R))
        (fun
          | .leaf i => Polynomial.C (MvPolynomial.X (.leaf i))
          | .output => Polynomial.X)).comp dehom) p
  apply MvPolynomial.hom_eq_hom
  · ext r
    simp [dehom]
  · intro v
    cases v with
    | leaf i a => cases a <;> simp [dehom]
    | output a => cases a <;> simp [dehom]

/-- Dehomogenization sends the frozen local operand to the independently
transcribed affine local operand. -/
theorem map_localSlice_dehom
    {R : Type*} [CommRing R] (i : ℕ) :
    (CryptoLean.Semaev.FrozenProjective.localSlice (R := R) i).map dehom =
      localSlice i := by
  simp [CryptoLean.Semaev.FrozenProjective.localSlice, localSlice,
    CryptoLean.Semaev.FrozenProjective.HValue, f3, dehom]
  ring

/-- Exact, non-tautological coefficient-unit-`1` identification of the
independent affine left-fold recurrence with the repository frozen family. -/
theorem dehom_frozenC_eq_semaevLeftFoldC
    {R : Type*} [CommRing R] (s : ℕ) :
    dehom (CryptoLean.Semaev.FrozenProjective.frozenC R s) = C R s := by
  induction s with
  | zero =>
      simp only [CryptoLean.Semaev.FrozenProjective.frozenC, C,
        CryptoLean.Semaev.FrozenProjective.HValue, f3,
        CryptoLean.Semaev.FrozenProjective.leafPair,
        CryptoLean.Semaev.FrozenProjective.outputPair, map_add, map_sub,
        map_mul, map_pow, dehom_X, map_ofNat]
      ring
  | succ s ih =>
      rw [CryptoLean.Semaev.FrozenProjective.frozenC, C]
      rw [← Polynomial.resultant_map_map]
      rw [map_outputSlice_dehom, map_localSlice_dehom, ih]

/-- Canonical affine representatives for the sixteen source coordinates. -/
def projectiveLeaves
    {K : Type*} [Field K] (x : Fin 16 → K) :
    ℕ → CryptoLean.Semaev.FrozenProjective.ProjectivePair K :=
  fun i => .affine (externalValue x i)

/-- Evaluation after coefficient-unit-one dehomogenization is exactly frozen
specialization at affine projective representatives. -/
theorem eval_dehom_eq_frozenSpecialize
    {K : Type*} [Field K]
    (x : Fin 16 → K) (X : K)
    (p : MvPolynomial CryptoLean.Semaev.FrozenProjective.Var K) :
    MvPolynomial.eval (assignment x X) (dehom p) =
      CryptoLean.Semaev.FrozenProjective.specialize
        (projectiveLeaves x) (.affine X) p := by
  change
    ((MvPolynomial.eval (assignment x X)).comp dehom) p =
      (CryptoLean.Semaev.FrozenProjective.specialize
        (projectiveLeaves x) (.affine X)) p
  apply MvPolynomial.hom_eq_hom
  · ext r
    simp [dehom, CryptoLean.Semaev.FrozenProjective.specialize]
  · intro v
    cases v with
    | leaf i a => cases a <;> simp [dehom, assignment, projectiveLeaves,
        CryptoLean.Semaev.FrozenProjective.specialize,
        CryptoLean.Semaev.FrozenProjective.assignment,
        CryptoLean.Semaev.FrozenProjective.ProjectivePair.coord,
        CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine]
    | output a => cases a <;> simp [dehom, assignment,
        CryptoLean.Semaev.FrozenProjective.specialize,
        CryptoLean.Semaev.FrozenProjective.assignment,
        CryptoLean.Semaev.FrozenProjective.ProjectivePair.coord,
        CryptoLean.Semaev.FrozenProjective.ProjectivePair.affine]

/-- The target-specialized source representative is exactly the repository
frozen specialization, with no unspecified scalar unit. -/
theorem S17At_eq_frozenSpecialize
    {K : Type*} [Field K]
    (x : Fin 16 → K) (X : K) :
    S17At x X =
      CryptoLean.Semaev.FrozenProjective.specialize
        (projectiveLeaves x) (.affine X)
        (CryptoLean.Semaev.FrozenProjective.frozenC K 14) := by
  rw [S17At, ← dehom_frozenC_eq_semaevLeftFoldC]
  exact eval_dehom_eq_frozenSpecialize x X _

end CryptoLean.Semaev.LeftFoldAffine
