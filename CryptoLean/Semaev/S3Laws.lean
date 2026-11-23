import Mathlib
import CryptoLean.Semaev.S3

-- Generic laws split out of the secp256k1 module; ported from KeyAIGit/ecdlp-lean-verification Ecdlp/Proved/SemaevThree.lean at 0a47cd62f43d (PR #347).
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

namespace CryptoLean.Semaev

variable {F : Type*} [CommRing F]

/-- `S3` is symmetric under swapping its first two `x`-arguments. -/
theorem S3_symm₁₂ (a b x₁ x₂ x₃ : F) : S3 a b x₁ x₂ x₃ = S3 a b x₂ x₁ x₃ := by
  simp only [S3]; ring

/-- `S3` is symmetric under swapping its last two `x`-arguments — together with
`S3_symm₁₂` this shows `S3` is fully symmetric, as a summation polynomial must be. -/
theorem S3_symm₂₃ (a b x₁ x₂ x₃ : F) : S3 a b x₁ x₂ x₃ = S3 a b x₁ x₃ x₂ := by
  simp only [S3]; ring

variable {K : Type*} [Field K]

/-- **Forward direction of Semaev's `S3` (chord case).** For a short Weierstrass curve
`y² = x³ + a·x + b` over a field: if `(x₁,y₁)` and `(x₂,y₂)` lie on the curve with
`x₁ ≠ x₂`, and `x₃` is the `x`-coordinate of their chord-sum — stated in the
cleared-denominator form `(x₁−x₂)²·(x₁+x₂+x₃) = (y₂−y₁)²`, i.e.
`x₃ = ((y₂−y₁)/(x₂−x₁))² − x₁ − x₂` — then `S3(x₁,x₂,x₃) = 0`.

Contrapositively: a triple `(x₁,x₂,x₃)` that is **not** a root of `S3` can never arise as
the `x`-coordinates of three collinear points of `E`. The proof is the certified two-step
elimination: `hchord` and the curve equations give `2·y₁·y₂ = T`; squaring and applying the
cofactor identity yields `(x₁−x₂)²·S3 = T² − 4·f₁·f₂ = 0`, and `(x₁−x₂)² ≠ 0` cancels. -/
theorem S3_eq_zero_of_chord (a b x₁ y₁ x₂ y₂ x₃ : K)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hx : x₁ ≠ x₂)
    (hchord : (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ - y₁) ^ 2) :
    S3 a b x₁ x₂ x₃ = 0 := by
  have hne : (x₁ - x₂) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  -- Step 1 (syzygy `N ≡ 2·y₁·y₂ − T`, with `N = 0` by `hchord`): `2·y₁·y₂ = T`.
  have hT : 2 * y₁ * y₂
      = (x₁ + x₂) * (x₁ * x₂ + a) + 2 * b - (x₁ - x₂) ^ 2 * x₃ := by
    linear_combination hchord + h₁ + h₂
  -- Step 2 (cofactor identity, using `T² = 4·y₁²·y₂² = 4·f₁·f₂`): `(x₁−x₂)²·S3 = 0`.
  have key : (x₁ - x₂) ^ 2 * S3 a b x₁ x₂ x₃ = 0 := by
    simp only [S3]
    linear_combination
      (-(((x₁ + x₂) * (x₁ * x₂ + a) + 2 * b - (x₁ - x₂) ^ 2 * x₃) + 2 * y₁ * y₂)) * hT
      + (4 * (x₂ ^ 3 + a * x₂ + b)) * h₁ + (4 * y₁ ^ 2) * h₂
  exact (mul_eq_zero.mp key).resolve_left hne

/-- **Forward direction of Semaev's `S3` (tangent / doubling case).** The `x₁ = x₂`
companion of `S3_eq_zero_of_chord`: if `(x₁,y₁)` is a curve point and `x₃` is the
`x`-coordinate of `2·(x₁,y₁)` — stated in the cleared-denominator doubling form
`4·y₁²·(x₃ + 2·x₁) = (3·x₁² + a)²`, i.e. `x₃ = ((3·x₁²+a)/(2·y₁))² − 2·x₁` — then
`S3(x₁,x₁,x₃) = 0` (equivalently `2P + P₃ = O ⇒ S3(x_P, x_P, x_{P₃}) = 0`).

Unlike the chord case there is no `y₁·y₂` cross term, so no cofactor cancellation is
needed: `S3(x₁,x₁,x₃)` collapses (via `S3_symm₁₂`/algebra) to `−4·f₁·x₃ + (x₁²−a)² − 8b·x₁`,
and substituting the doubling relation and the curve equation makes it vanish identically —
a single certified `linear_combination`. Together with `S3_eq_zero_of_chord` this proves the
forward direction of `S3` in every nondegenerate case. -/
theorem S3_eq_zero_of_tangent (a b x₁ y₁ x₃ : K)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b)
    (hdbl : 4 * y₁ ^ 2 * (x₃ + 2 * x₁) = (3 * x₁ ^ 2 + a) ^ 2) :
    S3 a b x₁ x₁ x₃ = 0 := by
  simp only [S3]
  linear_combination (4 * x₃ + 8 * x₁) * h₁ - hdbl

/-- **Reverse direction of Semaev's `S3` — the two roots.** As a polynomial in its third
argument `S3` is quadratic with leading coefficient `(x₁−x₂)²`, and (on the curve) its two
roots are exactly the `x`-coordinates of `P₁+P₂` and `P₁−P₂`. So if `(x₁,y₁), (x₂,y₂)` lie on
`y² = x³ + a·x + b` with `x₁ ≠ x₂` and `S3(x₁,x₂,x₃) = 0`, then `x₃` is one of those two:
`(x₁−x₂)²·x₃ = (y₂−y₁)² − (x₁+x₂)(x₁−x₂)²` (the cleared form of `x₃ = x(P₁+P₂)`) **or**
`(x₁−x₂)²·x₃ = (y₂+y₁)² − (x₁+x₂)(x₁−x₂)²` (the cleared `x₃ = x(P₁−P₂)`).

The proof is the certified master factorization `(x₁−x₂)²·S3 = (D·x₃−R₊)(D·x₃−R₋)` (an exact
`ring` identity modulo the curve equations, cofactors from a sympy Gröbner + resultant
certificate); with `S3 = 0`, one factor vanishes. (No `x₁ ≠ x₂` hypothesis is needed — at
`x₁ = x₂` on the curve, `R₊·R₋ = (y₂²−y₁²)² = 0`, so the disjunction still holds; the intended
use is nonetheless the chord case where `R₊,R₋` are genuine `x`-coordinates.) -/
theorem S3_root_of_eq_zero (a b x₁ y₁ x₂ y₂ x₃ : K)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hS : S3 a b x₁ x₂ x₃ = 0) :
    (x₁ - x₂) ^ 2 * x₃ = (y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2 ∨
    (x₁ - x₂) ^ 2 * x₃ = (y₂ + y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2 := by
  have hprod :
      ((x₁ - x₂) ^ 2 * x₃ - ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2))
    * ((x₁ - x₂) ^ 2 * x₃ - ((y₂ + y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2)) = 0 := by
    have hid :
        ((x₁ - x₂) ^ 2 * x₃ - ((y₂ - y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2))
      * ((x₁ - x₂) ^ 2 * x₃ - ((y₂ + y₁) ^ 2 - (x₁ + x₂) * (x₁ - x₂) ^ 2))
      = (x₁ - x₂) ^ 2 * S3 a b x₁ x₂ x₃ := by
      simp only [S3]
      linear_combination
        (-(2 * (x₁ - x₂) ^ 2 * x₃ + 2 * (x₁ + x₂) * (x₁ - x₂) ^ 2
            + (y₂ ^ 2 - y₁ ^ 2) + (x₂ ^ 3 - x₁ ^ 3) + a * (x₂ - x₁))) * h₁
        + (-(2 * (x₁ - x₂) ^ 2 * x₃ + 2 * (x₁ + x₂) * (x₁ - x₂) ^ 2
            - (y₂ ^ 2 - y₁ ^ 2) - (x₂ ^ 3 - x₁ ^ 3) - a * (x₂ - x₁))) * h₂
    rw [hid, hS, mul_zero]
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- **Semaev's `S3`, full characterization (iff).** Combining the forward direction
(`S3_eq_zero_of_chord`) with the reverse (`S3_root_of_eq_zero`): for points `(x₁,y₁), (x₂,y₂)`
on `y² = x³ + a·x + b` with `x₁ ≠ x₂`,
`S3(x₁,x₂,x₃) = 0` **iff** `x₃` is the `x`-coordinate of `P₁+P₂` or of `P₁−P₂` (in cleared
form). The `+` disjunct is literally the chord hypothesis of the forward direction; the `−`
disjunct is the same with `y₂ ↦ −y₂` (the point `−P₂`). This is the complete statement of
`S3` as the elimination of `y₁,y₂` from "three points sum to `O`". -/
theorem S3_eq_zero_iff (a b x₁ y₁ x₂ y₂ x₃ : K)
    (h₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (h₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hx : x₁ ≠ x₂) :
    S3 a b x₁ x₂ x₃ = 0 ↔
      (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ - y₁) ^ 2 ∨
      (x₁ - x₂) ^ 2 * (x₁ + x₂ + x₃) = (y₂ + y₁) ^ 2 := by
  constructor
  · intro hS
    rcases S3_root_of_eq_zero a b x₁ y₁ x₂ y₂ x₃ h₁ h₂ hS with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · rintro (h | h)
    · exact S3_eq_zero_of_chord a b x₁ y₁ x₂ y₂ x₃ h₁ h₂ hx h
    · exact S3_eq_zero_of_chord a b x₁ y₁ x₂ (-y₂) x₃ h₁ (by linear_combination h₂) hx
        (by linear_combination h)

end CryptoLean.Semaev
