import Mathlib
import CryptoLean.Secp256k1.Secp256k1Curve
import CryptoLean.Semaev.S3Laws

-- Ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/SemaevThree.lean at 0a47cd62f43d (PR #347).
/-!
# Semaev's third summation polynomial `S3`

Formalizes Semaev's 3rd summation polynomial for a short Weierstrass curve
`y² = x³ + a·x + b` and proves its **forward direction** in both nondegenerate cases:
whenever a field element `x₃` is the `x`-coordinate of the sum of two curve points
`(x₁,y₁), (x₂,y₂)` — the `x₁ ≠ x₂` "chord" case (`S3_eq_zero_of_chord`) or the `x₁ = x₂`
"tangent"/doubling case (`S3_eq_zero_of_tangent`) — the triple `(x₁,x₂,x₃)` is a root of
`S3`. Equivalently: if three affine points with these `x`-coordinates satisfy
`P₁ + P₂ + P₃ = O`, then `S3(x₁,x₂,x₃) = 0`.

Summation polynomials (Semaev, 2004) are the algebraic backbone of index-calculus /
Gröbner-basis attacks on ECDLP over extension fields; `Sₙ = 0` encodes the existence of
`n` curve points with prescribed `x`-coordinates summing to `O`, and `S3` is their base
case. To our knowledge this is the first formalization of a Semaev summation polynomial in
Lean/Mathlib. It is a **construction** (a barrier item in `BARRIERS.md`, "Semaev
polynomials"), not an attack: the forward implication is a necessary condition, and by
itself computes nothing about any discrete log — it enriches the verified substrate.

**Certificate provenance (Fable → kernel).** The two ring identities driving the proof —
the cofactor identity `(x₁−x₂)²·S3 = T² − 4·f₁·f₂` and the syzygy
`N = (2·y₁·y₂ − T) − (y₁²−f₁) − (y₂²−f₂)`, with `fᵢ = xᵢ³ + a·xᵢ + b`,
`T = (x₁+x₂)(x₁·x₂+a) + 2b − (x₁−x₂)²·x₃`, and `N = (x₁−x₂)²(x₁+x₂+x₃) − (y₂−y₁)²` —
were designed and verified by exact symbolic computation (sympy: Gröbner reduction plus an
independent iterated-resultant elimination) before transcription; here the Lean kernel
re-checks them via `linear_combination`/`ring`. The `y₁·y₂` cross term is eliminated by
conjugate multiplication, which is precisely why `S3` is sign-symmetric — it captures the
`x`-coordinate of both `P₁+P₂` and `P₁−P₂` (the two roots of `S3(x₁,x₂,·)`).
-/

namespace CryptoLean.Secp256k1.Semaev

open CryptoLean.Semaev

open CryptoLean.Secp256k1.Curve

variable [Fact (Nat.Prime Secp256k1.p)]

/-- **Semaev's `S3` for secp256k1 (`y² = x³ + 7`), forward direction.** Specialization of
`S3_eq_zero_of_chord` to the secp256k1 curve (`a = 0`, `b = 7`): if `(x₁,y₁)` and `(x₂,y₂)`
satisfy `y² = x³ + 7` with `x₁ ≠ x₂`, and `x₃` is the `x`-coordinate of their chord-sum,
then `(x₁,x₂,x₃)` is a root of secp256k1's third Semaev summation polynomial. -/
theorem secp256k1_semaev_three_chord
    (x₁ y₁ x₂ y₂ x₃ : ZMod Secp256k1.p)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + 7) (h₂ : y₂ ^ 2 = x₂ ^ 3 + 7)
    (hx : x₁ ≠ x₂)
    (hchord : (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ - y₁) ^ 2) :
    S3 (0 : ZMod Secp256k1.p) 7 x₁ x₂ x₃ = 0 :=
  S3_eq_zero_of_chord 0 7 x₁ y₁ x₂ y₂ x₃
    (by linear_combination h₁) (by linear_combination h₂) hx hchord

/-- **Semaev's `S3` for secp256k1 (`y² = x³ + 7`), tangent/doubling case.** Specialization
of `S3_eq_zero_of_tangent` to secp256k1 (`a = 0`, `b = 7`): if `(x₁,y₁)` satisfies
`y² = x³ + 7` and `x₃` is the `x`-coordinate of `2·(x₁,y₁)` (`4·y₁²·(x₃+2·x₁) = 9·x₁⁴`),
then `(x₁,x₁,x₃)` is a root of secp256k1's third Semaev summation polynomial. With
`secp256k1_semaev_three_chord`, secp256k1's `S3` forward direction is complete. -/
theorem secp256k1_semaev_three_tangent
    (x₁ y₁ x₃ : ZMod Secp256k1.p)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + 7)
    (hdbl : 4 * y₁ ^ 2 * (x₃ + 2 * x₁) = (3 * x₁ ^ 2) ^ 2) :
    S3 (0 : ZMod Secp256k1.p) 7 x₁ x₁ x₃ = 0 :=
  S3_eq_zero_of_tangent 0 7 x₁ y₁ x₃
    (by linear_combination h₁) (by linear_combination hdbl)

open WeierstrassCurve.Affine in
/-- **Semaev's `S3` for secp256k1, on actual curve points (chord case).** The point-group
form of `secp256k1_semaev_three_chord`: for genuine affine points of the Mathlib elliptic
curve `secp256k1.toAffine.Point`, if `P₁ + P₂ + P₃ = O` (the group identity) with
`x(P₁) ≠ x(P₂)`, then their `x`-coordinates `(x₁,x₂,x₃)` are a root of secp256k1's third
Semaev summation polynomial. This is the honest statement — the hypothesis is the actual
elliptic-curve group relation, not a raw coordinate equation. The proof unfolds Mathlib's
formalized chord addition (`Point.add_of_X_ne`, `slope_of_X_ne`, `addX`) to recover
`x₃ = x(P₁+P₂)`, clears the denominator, and applies `secp256k1_semaev_three_chord`. -/
theorem secp256k1_semaev_three_point
    {x₁ y₁ x₂ y₂ x₃ y₃ : ZMod Secp256k1.p}
    (h₁ : secp256k1.toAffine.Nonsingular x₁ y₁)
    (h₂ : secp256k1.toAffine.Nonsingular x₂ y₂)
    (h₃ : secp256k1.toAffine.Nonsingular x₃ y₃)
    (hx : x₁ ≠ x₂)
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    S3 (0 : ZMod Secp256k1.p) 7 x₁ x₂ x₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, Point.add_of_X_ne hx, Point.neg_some, Point.some.injEq] at hsum
  have hX := hsum.1
  rw [slope_of_X_ne hx] at hX
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hc₁ : y₁ ^ 2 = x₁ ^ 3 + 7 := by
    have he : secp256k1.toAffine.Equation x₁ y₁ := h₁.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [secp256k1] at he; linear_combination he
  have hc₂ : y₂ ^ 2 = x₂ ^ 3 + 7 := by
    have he : secp256k1.toAffine.Equation x₂ y₂ := h₂.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [secp256k1] at he; linear_combination he
  have hX2 : (y₁ - y₂) ^ 2 / (x₁ - x₂) ^ 2 = x₁ + x₂ + x₃ := by
    simp only [WeierstrassCurve.Affine.addX, secp256k1, div_pow] at hX
    linear_combination hX
  rw [div_eq_iff (pow_ne_zero 2 hd)] at hX2
  have hchord : (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ - y₁) ^ 2 := by
    linear_combination -hX2
  exact secp256k1_semaev_three_chord x₁ y₁ x₂ y₂ x₃ hc₁ hc₂ hx hchord

open WeierstrassCurve.Affine in
/-- **Semaev's `S3` for secp256k1, on actual curve points (tangent/doubling case).** The
`P₁ = P₂` companion of `secp256k1_semaev_three_point`: if `2•P₁ + P₃ = O` for genuine points
of `secp256k1.toAffine.Point` with `P₁` not `2`-torsion (`y₁ ≠ negY x₁ y₁`, i.e. `2·y₁ ≠ 0`),
then `S3(x₁,x₁,x₃) = 0`. Together with `secp256k1_semaev_three_point`, the `S3` forward
direction holds for Mathlib's formalized elliptic-curve group law in every nondegenerate case.
Unfolds the tangent doubling (`Point.add_of_Y_ne`, `slope_of_Y_ne`) to recover `x₃ = x(2P₁)`,
clears the denominator, and applies `secp256k1_semaev_three_tangent`. -/
theorem secp256k1_semaev_three_point_double
    {x₁ y₁ x₃ y₃ : ZMod Secp256k1.p}
    (h₁ : secp256k1.toAffine.Nonsingular x₁ y₁)
    (h₃ : secp256k1.toAffine.Nonsingular x₃ y₃)
    (hy : y₁ ≠ secp256k1.toAffine.negY x₁ y₁)
    (hsum : Point.some x₁ y₁ h₁ + Point.some x₁ y₁ h₁ + Point.some x₃ y₃ h₃ = 0) :
    S3 (0 : ZMod Secp256k1.p) 7 x₁ x₁ x₃ = 0 := by
  rw [add_eq_zero_iff_eq_neg, Point.add_of_Y_ne hy, Point.neg_some, Point.some.injEq] at hsum
  have hX := hsum.1
  have hnegY : secp256k1.toAffine.negY x₁ y₁ = -y₁ := by
    simp [WeierstrassCurve.Affine.negY, secp256k1]
  have h2y : (2 : ZMod Secp256k1.p) * y₁ ≠ 0 := by
    have hd : y₁ - secp256k1.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    rw [hnegY] at hd; intro hc; exact hd (by linear_combination hc)
  have hslope : secp256k1.toAffine.slope x₁ x₁ y₁ y₁ = 3 * x₁ ^ 2 / (2 * y₁) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy, hnegY]
    simp only [secp256k1, mul_zero, zero_mul, add_zero, sub_zero]
    rw [show y₁ - -y₁ = 2 * y₁ from by ring]
  have hc₁ : y₁ ^ 2 = x₁ ^ 3 + 7 := by
    have he : secp256k1.toAffine.Equation x₁ y₁ := h₁.1
    rw [WeierstrassCurve.Affine.equation_iff] at he
    simp only [secp256k1] at he; linear_combination he
  rw [hslope] at hX
  have hX2 : (3 * x₁ ^ 2) ^ 2 / (2 * y₁) ^ 2 = x₃ + 2 * x₁ := by
    simp only [WeierstrassCurve.Affine.addX, secp256k1, div_pow] at hX
    linear_combination hX
  rw [div_eq_iff (pow_ne_zero 2 h2y)] at hX2
  have hdbl : 4 * y₁ ^ 2 * (x₃ + 2 * x₁) = (3 * x₁ ^ 2) ^ 2 := by
    linear_combination -hX2
  exact secp256k1_semaev_three_tangent x₁ y₁ x₃ hc₁ hdbl

/-- **Semaev's `S3` for secp256k1 (`y² = x³ + 7`), full characterization (iff).**
Specialization of `S3_eq_zero_iff` to secp256k1: for points `(x₁,y₁), (x₂,y₂)` on the curve
with `x₁ ≠ x₂`, `S3(x₁,x₂,x₃) = 0` iff `x₃` is the `x`-coordinate of `P₁+P₂` or of `P₁−P₂`
(cleared form). This is the complete `S3` characterization for secp256k1 — forward and
reverse together. -/
theorem secp256k1_semaev_three_iff
    (x₁ y₁ x₂ y₂ x₃ : ZMod Secp256k1.p)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + 7) (h₂ : y₂ ^ 2 = x₂ ^ 3 + 7) (hx : x₁ ≠ x₂) :
    S3 (0 : ZMod Secp256k1.p) 7 x₁ x₂ x₃ = 0 ↔
      (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ - y₁) ^ 2 ∨
      (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ + y₁) ^ 2 :=
  S3_eq_zero_iff 0 7 x₁ y₁ x₂ y₂ x₃ (by linear_combination h₁) (by linear_combination h₂) hx

end CryptoLean.Secp256k1.Semaev
