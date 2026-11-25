import Mathlib

/-!
# Open problems about elliptic curves and rational points

ProofAtlas problems (releaseRank) 6, 62, 102, 125, 140, 151, 171, 173, 211, 252.

**All ten problems are OPEN** (some with solved subcases). Each one that Mathlib can express
appears below only as an unproved `def … : Prop` whose docstring quotes the ProofAtlas
`exactTarget` and lists the modelling choices. Nothing in this file proves, or claims progress
towards, any of them. Finite verifications are labelled as finite checks; they are not partial
progress on the infinite statements.

Mathlib objects reused (no re-definitions):
* `WeierstrassCurve`, `WeierstrassCurve.IsElliptic`, `WeierstrassCurve.j`,
  `WeierstrassCurve.Δ`;
* `WeierstrassCurve.Affine.Point` (the Mordell–Weil group, with its `AddCommGroup`
  structure), `WeierstrassCurve.Affine.Point.map` (functoriality in the field; used for the
  Galois action), `WeierstrassCurve.Affine.equation_iff_nonsingular`;
* `WeierstrassCurve.LFunction`, `WeierstrassCurve.LSeries` (the Hasse–Weil L-function as a
  formal Euler product / Dirichlet series, with the local minimal model at each prime);
* `Field.absoluteGaloisGroup`, `ContRepresentation`, `TopRep`, `continuousCohomology` and
  `ContinuousCohomology.tateShafarevich` (the Tate–Shafarevich group of a Galois module:
  intersection of the kernels of the restriction maps along
  `Field.absoluteGaloisGroup.map (algebraMap K K_v)`), `NumberField.InfinitePlace.Completion`,
  `IsDedekindDomain.HeightOneSpectrum.adicCompletion` (used for problem 62);
* `analyticOrderAt`, `Module.rank`, `ComputablePred`, `Projectivization`,
  `MvPolynomial.IsHomogeneous`, `AlgebraicClosure`, `NumberField`;
* `not_fermat_42` (Fermat: `a⁴ + b⁴ ≠ c²`), `PythagoreanTriple.coprime_classification'`,
  `Int.sq_of_gcd_eq_one`.

## What is missing from Mathlib (gap notes)

* **Problem 125 (torsion conjecture for abelian varieties, `g ≥ 2`) is not stated here.**
  Mathlib has no abelian varieties (proper geometrically integral group schemes) over a number
  field, no dimension `g` for them, and no group `A(K)` of `K`-points with its torsion
  subgroup. Restricting to Jacobians of explicit curves would be a different statement.
* **Problem 151 (uniform boundedness for curves of genus `g ≥ 2`) is not stated here.**
  Mathlib has schemes, but not smooth projective geometrically integral curves over a number
  field together with their (arithmetic or geometric) **genus**. Restricting to plane or
  hyperelliptic models would be a weaker, non-equivalent statement.
* **Problem 173 (parity conjecture) is not stated here.** Mathlib has the Mordell–Weil group
  `E(K)` (and so `Module.rank ℤ E(K)`), but not the **local Weil–Deligne root numbers**
  `w(E/K_v)` (epsilon factors of the Weil–Deligne representation attached to `E/K_v`,
  including the wild cases at `v ∣ 2, 3`) nor the global root number `w(E/K)`. Defining `w`
  through a functional equation of `L(E/K, s)` is excluded by the quoted statement (and the
  functional equation is not in Mathlib either).
* **Problem 252 (Frey–Mazur) is not stated here.** The hypothesis `E[p] ≅ E'[p]` as
  `G_ℚ`-modules is expressible (an `AddEquiv` of `p`-torsion subgroups of the points over
  `AlgebraicClosure ℚ` commuting with `WeierstrassCurve.Affine.Point.map σ`), but the
  conclusion is not: Mathlib has no **isogenies** of elliptic curves (non-constant morphisms of
  curves preserving the origin), hence no relation "`ℚ`-isogenous". Replacing it by Faltings'
  criterion (equal traces of Frobenius at almost all primes) would rest on a deep theorem that
  is not in Mathlib, so no substitute Prop is offered.
* **Analytic continuation of `L(E, s)`** (modularity, Wiles–Taylor–Breuil–Conrad–Diamond) is
  not in Mathlib: `WeierstrassCurve.LSeries` is the Dirichlet series `∑ aₙ n^{-s}`, which is
  the junk value `0` where it does not converge. Problem 6 is therefore stated with an explicit
  entire continuation; see its docstring.
* **The endomorphism ring of an elliptic curve** (and so "CM" as `End_{ℚ̄}(E) ≠ ℤ`) is not in
  Mathlib. Problem 211 uses the classical list of the 13 CM `j`-invariants over `ℚ`; see its
  docstring.
* **The classical Tate–Shafarevich group of an elliptic curve** is not packaged in Mathlib
  (its own TODO: "Define the classical Tate–Shafarevich group in EllipticCurve"). Problem 62
  is stated by assembling it from the general `ContinuousCohomology.tateShafarevich`; the only
  new pieces are the `G_K`-module `E(K̄)` with the discrete topology (`galoisPointsModule`) and
  the family of completions of `K` at all places (`completionAt`). See its docstring.
* **Tunnell's theorem** (the forward direction of his criterion, via Waldspurger and
  Coates–Wiles) and **Mordell's theorem** are not in Mathlib and are *not* formalised here.

## Known results proved here

* `isCongruent_iff_exists_point` — `n > 0` is congruent iff `y² = x³ − n²x` has a rational
  point with `y ≠ 0` (both directions; classical).
* `isCongruent_iff_mul_sq` — congruence depends only on the square class of `n`.
* `isCongruent_five`, `isCongruent_six`, `isCongruent_seven`, `isCongruent_thirteen`,
  `isCongruent_fourteen`, `isCongruent_fifteen` — explicit rational right triangles.
* `not_fourth_sub_fourth_eq_sq` (Fermat's right-triangle theorem in the form
  `x⁴ − y⁴ ≠ z²`, by infinite descent), `not_fourth_add_four_fourth_eq_sq`
  (`X⁴ + 4Y⁴ ≠ Z²`).
* `not_isCongruent_one` (Fermat) and `not_isCongruent_two` (via Mathlib's `not_fermat_42`).
* `isElliptic_congruentCurve` — the congruent-number curve is an elliptic curve for `n ≠ 0`.

## Finite checks (labelled as such)

* `tunnellCriterion_finite_check` — for the squarefree `n ≤ 15`, Tunnell's criterion holds
  exactly for `n ∈ {5, 6, 7, 13, 14, 15}`. This concerns `TunnellCriterion` only (the
  non-congruence of `3, 10, 11` is not proved here); it is not evidence for the general
  statement.
-/

namespace CryptoLean.OpenProblems.NumberTheory.EllipticCurves

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## Problem 6: the Birch and Swinnerton-Dyer conjecture -/

/-- **ProofAtlas problem 6 (Birch and Swinnerton-Dyer Conjecture), OPEN.**

Quoted `exactTarget`: "Prove or disprove that, for every elliptic curve E over the rational
numbers, the rank of the finitely generated abelian group E(Q) of rational points equals the
order of vanishing at s = 1 of the associated Hasse–Weil L-function L(E, s)."

Modelling choices:
* an elliptic curve over `ℚ` is a `WeierstrassCurve ℚ` with `IsElliptic` (every elliptic curve
  over `ℚ` has such a model; the rank and `L(E, s)` are isomorphism invariants);
* `E(ℚ)` is `W.toAffine.Point` and its rank is `Module.rank ℤ E(ℚ)` (Mordell's theorem, that
  this is finite, is not in Mathlib; the statement asserts the rank equals a natural number);
* `L(E, s)` is Mathlib's `WeierstrassCurve.LSeries` (Euler product over all primes with the
  local minimal model; good/split/non-split/additive factors) on `Re s > 3/2`, where it
  converges absolutely by the Hasse bound. Since the analytic continuation (modularity) is not
  in Mathlib, the Prop asserts the existence of an **entire** function `F` agreeing with it on
  `Re s > 3/2` whose order of vanishing at `s = 1` is the rank. By the identity theorem such an
  `F` is unique, and by modularity it exists, so this Prop is equivalent to the quoted
  conjecture (the "prove" alternative). -/
def BirchSwinnertonDyer : Prop :=
  ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic], ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    (∀ s : ℂ, 3 / 2 < s.re → F s = W.LSeries s) ∧
    ∃ r : ℕ, analyticOrderAt F 1 = r ∧ Module.rank ℤ W.toAffine.Point = r

/-! ## Problem 62: finiteness of the Tate–Shafarevich group -/

section TateShafarevich

open scoped Classical
open NumberField

variable {K : Type} [Field K] (W : WeierstrassCurve K)

/-- The points `E(K̄)` of `W` over the algebraic closure `K̄` of `K` (an abbreviation; the
discrete topology below is a local instance only). -/
abbrev PointsOverClosure : Type := (W.baseChange (AlgebraicClosure K)).toAffine.Point

local instance : TopologicalSpace (PointsOverClosure W) := ⊥
local instance : DiscreteTopology (PointsOverClosure W) := ⟨rfl⟩

/-- The Galois action of `G_K = Gal(K̄/K)` on `E(K̄)`, `σ • P = Point.map σ P` (coordinatewise),
as a representation by continuous `ℤ`-linear maps of the discrete group `E(K̄)`. -/
noncomputable def galoisPointsAction :
    ContRepresentation ℤ (Field.absoluteGaloisGroup K) (PointsOverClosure W) :=
  .ofMonoidHom
  { toFun := fun σ =>
      { toLinearMap := (Point.map (W' := W)
          (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from σ).toAlgHom).toIntLinearMap
        cont := continuous_of_discreteTopology }
    map_one' := by ext P; cases P <;> rfl
    map_mul' := fun σ τ => by ext P; cases P <;> rfl }

/-- The discrete `G_K`-module `E(K̄)`, as an object of `TopRep ℤ G_K`. -/
noncomputable def galoisPointsModule : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of (galoisPointsAction W)

/-- The places of a number field `K`: the infinite places and the finite places (nonzero
primes of `𝓞 K`). -/
abbrev Place (K : Type) [Field K] [NumberField K] : Type :=
  InfinitePlace K ⊕ IsDedekindDomain.HeightOneSpectrum (𝓞 K)

variable [NumberField K]

/-- The completion `K_v` of `K` at a place `v` (`ℝ` or `ℂ` at an infinite place, the
`𝔭`-adic completion at a finite place). -/
abbrev completionAt : Place K → Type
  | .inl v => v.Completion
  | .inr v => v.adicCompletion K

noncomputable instance (v : Place K) : Field (completionAt v) := by
  cases v <;> (dsimp [completionAt]; infer_instance)

noncomputable instance (v : Place K) : Algebra K (completionAt v) := by
  cases v <;> (dsimp [completionAt]; infer_instance)

/-- `Ш(E/K)`: the elements of `H¹(G_K, E(K̄))` (continuous cohomology) that restrict to zero
in `H¹(G_{K_v}, E(K̄))` for every place `v` of `K`, via Mathlib's
`ContinuousCohomology.tateShafarevich`. -/
noncomputable def tateShafarevichGroup :
    AddSubgroup (continuousCohomology 1 (galoisPointsModule W)) :=
  ContinuousCohomology.tateShafarevich (completionAt (K := K)) (galoisPointsModule W) 1

end TateShafarevich

/-- **ProofAtlas problem 62 (Finiteness of the Tate-Shafarevich Group for Elliptic Curves),
OPEN.**

Quoted `exactTarget`: "Prove that the Tate-Shafarevich group Sha(E/K) is finite for every
elliptic curve E defined over a number field K."

Modelling choices:
* a number field is a `Type` with `Field` and `NumberField`; an elliptic curve over `K` is a
  `WeierstrassCurve K` with `IsElliptic` (every elliptic curve has such a model, and `Ш` is an
  isomorphism invariant);
* `G_K` is Mathlib's `Field.absoluteGaloisGroup K = Gal(K̄/K)` with its Krull topology; since
  `K` has characteristic `0`, `K̄ = K^sep`;
* `E(K̄)` carries the discrete topology and the action `σ ↦ Point.map σ`; `H¹` is Mathlib's
  continuous cohomology (continuous = locally constant cochains);
* `Ш(E/K)` is `ContinuousCohomology.tateShafarevich` over **all** places (infinite and finite)
  with `K_v` the completion. As in Mathlib's implementation notes, the local groups are
  `H¹(G_{K_v}, E(K̄))` (restriction along `G_{K_v} → G_K`) rather than `H¹(G_{K_v}, E(K̄_v))`;
  the comparison map between them is injective (Milne, *Arithmetic Duality Theorems*,
  Remark I.3.10), so the kernels, and hence `Ш`, agree with the classical definition;
* "finite" is `Finite` of the subgroup. -/
def ShaFinite : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic],
    Finite (tateShafarevichGroup W)

/-! ## Problem 102: unbounded ranks -/

/-- **ProofAtlas problem 102 (Unbounded Ranks of Elliptic Curves over Q), OPEN.**

Quoted `exactTarget`: "Prove that for EVERY nonnegative integer r there is SOME elliptic curve
E/Q whose actual Mordell-Weil group E(Q) has Z-rank at least r. The base field is exactly Q and
rank means the free abelian rank in Mordell's theorem, not analytic rank, a Selmer bound or
random-matrix corank. Thus the set of actual ranks of ALL elliptic curves over Q is unbounded.
Counting one representative per Q-isomorphism class does not alter this existence question. No
effective construction, specified family, uniform curve-producing algorithm or predetermined
rate of growth is required."

Modelling choices: elliptic curves over `ℚ` are `WeierstrassCurve ℚ` with `IsElliptic`;
`E(ℚ)` is `W.toAffine.Point`; the `ℤ`-rank is `Module.rank ℤ E(ℚ)` (a cardinal; "at least
`r`" is `r ≤ rank`, which is meaningful without Mordell's theorem). -/
def UnboundedRanks : Prop :=
  ∀ r : ℕ, ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
    (r : Cardinal) ≤ Module.rank ℤ W.toAffine.Point

/-! ## Problem 140: the congruent number problem -/

/-- A positive integer `n` is a **congruent number** if it is the area of a right triangle with
three rational sides. -/
def IsCongruent (n : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- **ProofAtlas problem 140 (Congruent Number Problem), OPEN (with solved subcases).**

Quoted `exactTarget`: "Determine exactly which positive integers are congruent numbers, i.e.
areas of right triangles with all three sides rational, equivalently for which squarefree n the
elliptic curve y^2 = x^3 - n^2 x has a rational point with y != 0."

Modelling choice: "determine exactly which" is read as the existence of an **algorithm**
deciding, for every natural number `n`, whether `n` is congruent (`ComputablePred`). This is an interpretation of a "determine" target: a decision
procedure is neither necessary nor sufficient for what the literature would count as a
solution (e.g. an explicit criterion such as Tunnell's). The
equivalence with the elliptic-curve formulation is `isCongruent_iff_exists_point` below, and
the reduction to squarefree `n` is `isCongruent_iff_mul_sq`. (Under BSD, Tunnell's criterion
gives such an algorithm; see `tunnellConverse`.) -/
def CongruentNumberProblem : Prop :=
  ComputablePred fun n : ℕ => IsCongruent n

/-- The number of integer solutions of `a x² + b y² + c z² = n`. The search box
`|x|, |y|, |z| ≤ √n` contains every solution when `a, b, c ≥ 1`, the only case used below. -/
def tunnellCount (a b c n : ℕ) : ℕ :=
  let B : Finset ℤ := Finset.Icc (-(Nat.sqrt n : ℤ)) (Nat.sqrt n)
  ((B ×ˢ B ×ˢ B).filter fun p => (a : ℤ) * p.1 ^ 2 + b * p.2.1 ^ 2 + c * p.2.2 ^ 2 = n).card

/-- **Tunnell's criterion** for a squarefree `n`: for odd `n`,
`#{2x² + y² + 8z² = n} = 2 · #{2x² + y² + 32z² = n}`; for even `n`,
`#{4x² + y² + 8z² = n/2} = 2 · #{4x² + y² + 32z² = n/2}`. -/
def TunnellCriterion (n : ℕ) : Prop :=
  if n % 2 = 1 then tunnellCount 2 1 8 n = 2 * tunnellCount 2 1 32 n
  else tunnellCount 4 1 8 (n / 2) = 2 * tunnellCount 4 1 32 (n / 2)

instance (n : ℕ) : Decidable (TunnellCriterion n) := by
  unfold TunnellCriterion; infer_instance

/-- **The converse of Tunnell's theorem, OPEN** (a refinement of problem 140, not the quoted
target itself). Tunnell (1983) proved that a congruent squarefree `n` satisfies
`TunnellCriterion n` (not in Mathlib); the converse is known to follow from the
Birch–Swinnerton-Dyer conjecture for `y² = x³ − n²x` and is open in general. -/
def tunnellConverse : Prop :=
  ∀ n : ℕ, 0 < n → Squarefree n → TunnellCriterion n → IsCongruent n

/-- The congruent-number curve `y² = x³ − n² x`. -/
def congruentCurve (n : ℚ) : WeierstrassCurve ℚ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -n ^ 2, a₆ := 0 }

lemma congruentCurve_Δ (n : ℚ) : (congruentCurve n).Δ = 64 * n ^ 6 := by
  simp [congruentCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]; ring

/-- Known result: `y² = x³ − n²x` is an elliptic curve for `n ≠ 0` (`Δ = 64 n⁶`). -/
theorem isElliptic_congruentCurve {n : ℚ} (hn : n ≠ 0) : (congruentCurve n).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, congruentCurve_Δ]
  exact (by positivity : (64 : ℚ) * n ^ 6 ≠ 0).isUnit

lemma congruentCurve_equation (n x y : ℚ) :
    (congruentCurve n).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  rw [Affine.equation_iff]; simp [congruentCurve]; constructor <;> intro h <;> linarith

lemma congruentCurve_nonsingular {n : ℚ} (hn : n ≠ 0) (x y : ℚ) :
    (congruentCurve n).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  have := isElliptic_congruentCurve hn
  rw [← Affine.equation_iff_nonsingular, congruentCurve_equation]

/-- **Known result** (classical; e.g. Koblitz, *Introduction to Elliptic Curves and Modular
Forms*, Ch. I §2, Prop. 18): a positive integer `n` is congruent iff the elliptic curve
`y² = x³ − n²x` has a rational (nonsingular affine) point with `y ≠ 0`. -/
theorem isCongruent_iff_exists_point {n : ℕ} (hn : 0 < n) :
    IsCongruent n ↔ ∃ x y : ℚ, y ≠ 0 ∧ (congruentCurve n).toAffine.Nonsingular x y := by
  have hn' : (n : ℚ) ≠ 0 := by positivity
  simp_rw [congruentCurve_nonsingular hn']
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hpy, hab⟩
    have hca : c - a ≠ 0 := by
      intro h
      have : c = a := by linarith
      subst this; nlinarith
    refine ⟨n * b / (c - a), 2 * n ^ 2 / (c - a), by positivity, ?_⟩
    rw [← hab]
    field_simp
    linear_combination (-1 : ℚ) * hpy
  · rintro ⟨x, y, hy, h⟩
    have hy2 : 0 < y ^ 2 := by positivity
    have hx : x * (x ^ 2 - n ^ 2) = y ^ 2 := by rw [h]; ring
    refine ⟨|x ^ 2 - n ^ 2| / |y|, |2 * n * x| / |y|, (x ^ 2 + n ^ 2) / |y|, ?_, ?_, ?_, ?_, ?_⟩
    · have : x ^ 2 - n ^ 2 ≠ 0 := by
        intro h0; rw [h0] at hx; simp at hx
        exact hy (pow_eq_zero_iff two_ne_zero |>.mp hx.symm)
      positivity
    · have : x ≠ 0 := by
        intro h0; rw [h0] at hx; simp at hx
        exact hy (pow_eq_zero_iff two_ne_zero |>.mp hx.symm)
      positivity
    · have : x ^ 2 + n ^ 2 > 0 := by positivity
      positivity
    · rw [div_pow, div_pow, div_pow, sq_abs, sq_abs, sq_abs]
      field_simp; ring
    · rw [div_mul_div_comm, ← abs_mul, ← abs_mul, ← sq, abs_of_pos hy2]
      have : (x ^ 2 - n ^ 2) * (2 * n * x) = 2 * n * y ^ 2 := by rw [← hx]; ring
      rw [this, abs_of_pos (by positivity)]
      field_simp

/-- **Known result** (classical): `n` is congruent iff `n k²` is, for `k > 0` (scale the
triangle by `k`). Hence the congruent number problem reduces to squarefree `n`. -/
theorem isCongruent_iff_mul_sq (n : ℕ) {k : ℕ} (hk : 0 < k) :
    IsCongruent n ↔ IsCongruent (n * k ^ 2) := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨a, b, c, ha, hb, hc, hpy, hab⟩
    refine ⟨k * a, k * b, k * c, by positivity, by positivity, by positivity, ?_, ?_⟩
    · linear_combination (k : ℚ) ^ 2 * hpy
    · push_cast; linear_combination (k : ℚ) ^ 2 * hab
  · rintro ⟨a, b, c, ha, hb, hc, hpy, hab⟩
    refine ⟨a / k, b / k, c / k, by positivity, by positivity, by positivity, ?_, ?_⟩
    · field_simp; linear_combination hpy
    · push_cast at hab; field_simp; linear_combination 2 * hab

/-- **Known result**: 5 is congruent (Fibonacci): the triangle `(3/2, 20/3, 41/6)`. -/
theorem isCongruent_five : IsCongruent 5 :=
  ⟨3 / 2, 20 / 3, 41 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Known result**: 6 is congruent: the triangle `(3, 4, 5)`. -/
theorem isCongruent_six : IsCongruent 6 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Known result**: 7 is congruent: the triangle `(24/5, 35/12, 337/60)`. -/
theorem isCongruent_seven : IsCongruent 7 :=
  ⟨24 / 5, 35 / 12, 337 / 60, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Known result**: 13 is congruent: the triangle `(780/323, 323/30, 106921/9690)`. -/
theorem isCongruent_thirteen : IsCongruent 13 :=
  ⟨780 / 323, 323 / 30, 106921 / 9690, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- **Known result**: 14 is congruent: the triangle `(21/2, 8/3, 65/6)`. -/
theorem isCongruent_fourteen : IsCongruent 14 :=
  ⟨21 / 2, 8 / 3, 65 / 6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Known result**: 15 is congruent: the triangle `(4, 15/2, 17/2)`. -/
theorem isCongruent_fifteen : IsCongruent 15 :=
  ⟨4, 15 / 2, 17 / 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### Fermat's descent: `1` and `2` are not congruent -/

private lemma sq_or_neg_sq_of_gcd {k n w : ℤ} (h : Int.gcd k n = 1) (hkn : k * n = w ^ 2) :
    ∃ K, k ^ 2 = K ^ 4 ∧ (k = K ^ 2 ∨ k = -K ^ 2) := by
  obtain ⟨K, hK⟩ := Int.sq_of_gcd_eq_one h hkn
  refine ⟨K, ?_, hK⟩
  rcases hK with hK | hK <;> subst hK <;> ring

private lemma isCoprime_two_of_odd {x : ℤ} (hx : x % 2 = 1) : IsCoprime x 2 :=
  ⟨1, -(x / 2), by omega⟩

/-- Descent step: a primitive solution of `x⁴ + 4y⁴ = z²` with `x` odd yields a solution of
`M⁴ − N⁴ = R²` with `M² < z²`. -/
private lemma sumStep {x y z : ℤ} (hcop : Int.gcd x y = 1) (hx : x % 2 = 1) (hy : y ≠ 0)
    (h : x ^ 4 + 4 * y ^ 4 = z ^ 2) :
    ∃ M N R : ℤ, N ≠ 0 ∧ R ≠ 0 ∧ M ^ 4 - N ^ 4 = R ^ 2 ∧ M ^ 2 < z ^ 2 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hz : 0 < |z| := by
    rw [abs_pos]; rintro rfl; have : 0 < y ^ 4 := by positivity
    nlinarith [pow_two_nonneg (x ^ 2)]
  have hpt : PythagoreanTriple (x ^ 2) (2 * y ^ 2) |z| := by
    unfold PythagoreanTriple; rw [abs_mul_abs_self]; linear_combination h
  have hcop' : Int.gcd (x ^ 2) (2 * y ^ 2) = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
    exact (IsCoprime.mul_right (isCoprime_two_of_odd hx) hcop.pow_right).pow_left
  have hx2 : x ^ 2 % 2 = 1 := by
    have := (Int.odd_iff.mpr hx).pow (n := 2); exact Int.odd_iff.mp this
  obtain ⟨m, n, h1, h2, h3, hmn, -, hm0⟩ :=
    PythagoreanTriple.coprime_classification' hpt hcop' hx2 hz
  have hmny : m * n = y ^ 2 := by linarith
  have hy2 : 0 < y ^ 2 := by positivity
  have hm : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · subst h; simp at hmny; exact absurd hmny.symm hy2.ne'
  have hn : 0 < n := by nlinarith
  obtain ⟨M, -, hM | hM⟩ := sq_or_neg_sq_of_gcd hmn hmny
  swap; · nlinarith [sq_nonneg M]
  obtain ⟨N, -, hN | hN⟩ :=
    sq_or_neg_sq_of_gcd (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact hmny)
  swap; · nlinarith [sq_nonneg N]
  refine ⟨M, N, x, ?_, hx0, ?_, ?_⟩
  · rintro rfl; simp at hN; omega
  · rw [h1, hM, hN]; ring
  · have hz2 : z ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by rw [← h3, sq_abs]
    rw [hz2, ← hM]; nlinarith

/-- Splitting step: `y² = 2mn` with `m` even, `n` odd, coprime, gives `m² + n² = u⁴ + 4v⁴`. -/
private lemma splitStep {m n y : ℤ} (hm : m % 2 = 0) (hn : n % 2 = 1) (hcop : Int.gcd m n = 1)
    (hpos : 0 < m * n) (hy : y ^ 2 = 2 * m * n) :
    ∃ u v : ℤ, u % 2 = 1 ∧ v ≠ 0 ∧ Int.gcd u v = 1 ∧ m ^ 2 + n ^ 2 = u ^ 4 + 4 * v ^ 4 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have hye : Even y := by
    have : Even (y ^ 2) := ⟨2 * k * n, by rw [hy]; ring⟩
    exact (Int.even_pow.mp this).1
  obtain ⟨w, rfl⟩ := hye
  have hkn : k * n = w ^ 2 := by linarith
  have hcopk : Int.gcd k n = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢; exact hcop.of_mul_left_right
  obtain ⟨K, hK4, hK⟩ := sq_or_neg_sq_of_gcd hcopk hkn
  obtain ⟨N, hN4, hN⟩ :=
    sq_or_neg_sq_of_gcd (by rwa [Int.gcd_comm]) (by rw [mul_comm]; exact hkn)
  refine ⟨N, K, ?_, ?_, ?_, ?_⟩
  · have hodd : Odd (N ^ 2) := by
      rcases hN with h | h
      · rw [← h]; exact Int.odd_iff.mpr hn
      · have : Odd (-n) := (Int.odd_iff.mpr hn).neg
        rw [h, neg_neg] at this; exact this
    exact Int.odd_iff.mp ((Int.odd_pow.mp hodd).resolve_right (by norm_num))
  · rintro rfl; rcases hK with h | h <;> simp at h <;> subst h <;> simp at hpos
  · have hc : IsCoprime k n := Int.isCoprime_iff_gcd_eq_one.mpr hcopk
    have hc2 : IsCoprime (K ^ 2) (N ^ 2) := by
      rcases hK with h | h <;> rcases hN with h' | h' <;> rw [h, h'] at hc <;>
        simpa only [IsCoprime.neg_left_iff, IsCoprime.neg_right_iff] using hc
    exact Int.isCoprime_iff_gcd_eq_one.mp ((IsCoprime.pow_iff two_pos two_pos).mp hc2).symm
  · rw [mul_pow, hK4, hN4]; ring

private lemma gcd_reduce {x y : ℤ} (hx : x ≠ 0) :
    ∃ g : ℕ, 0 < g ∧ ∃ x' y' : ℤ, Int.gcd x' y' = 1 ∧ x = x' * g ∧ y = y' * g := by
  obtain ⟨g, x', y', hg, hc, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx)
  exact ⟨g, hg, x', y', hc, rfl, rfl⟩

/-- **Known result** (Fermat's right-triangle theorem, in Euler's form; e.g. Hardy–Wright,
*An Introduction to the Theory of Numbers*, Thm. 226 and its proof): `x⁴ − y⁴ = z²` has no
solution in integers with `y ≠ 0` and `z ≠ 0`. Proved here by infinite descent. -/
theorem not_fourth_sub_fourth_eq_sq {x y z : ℤ} (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  suffices H : ∀ k : ℕ, ∀ x y z : ℤ, x.natAbs = k → y ≠ 0 → z ≠ 0 →
      x ^ 4 - y ^ 4 = z ^ 2 → False
    from fun h => H _ x y z rfl hy hz h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x y z hk hy hz h
  have hx : x ≠ 0 := by
    rintro rfl; have : 0 < y ^ 4 := by positivity
    nlinarith [sq_nonneg z]
  obtain ⟨g, hg, x, y, hcop, rfl, rfl⟩ := gcd_reduce (y := y) hx
  have hg4 : ((g : ℤ) ^ 2) ^ 2 ∣ z ^ 2 := ⟨x ^ 4 - y ^ 4, by rw [← h]; ring⟩
  obtain ⟨z', rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hg4
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have h' : x ^ 4 - y ^ 4 = z' ^ 2 := by
    have : (g : ℤ) ^ 4 * (x ^ 4 - y ^ 4 - z' ^ 2) = 0 := by linear_combination h
    have := (mul_eq_zero.mp this).resolve_left (by positivity); linarith
  have hy' : y ≠ 0 := by rintro rfl; simp at hy
  have hz' : z' ≠ 0 := by rintro rfl; simp at hz
  have hx' : x ≠ 0 := by rintro rfl; simp at hx
  rcases (Nat.one_le_iff_ne_zero.mpr hg.ne').lt_or_eq with hg2 | hg1
  · -- a proper common factor: descend to the primitive solution
    refine ih x.natAbs ?_ x y z' rfl hy' hz' h'
    rw [← hk, Int.natAbs_mul]; simp only [Int.natAbs_natCast]
    have : 0 < x.natAbs := Int.natAbs_pos.mpr hx'
    nlinarith
  subst hg1
  simp only [Nat.cast_one, mul_one] at hk h' ⊢
  have hcopI : IsCoprime x y := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hcop4 : IsCoprime (y ^ 4) (z' ^ 2) := by
    rw [← h']
    have := (hcopI.pow (m := 4) (n := 4)).symm
    convert this.add_mul_left_right (-1) using 1; ring
  have hcopyz : IsCoprime (y ^ 2) z' := by
    rw [← IsCoprime.pow_iff two_pos two_pos]; simpa [← pow_mul] using hcop4
  have hx2pos : 0 < x ^ 2 := by positivity
  rcases Int.emod_two_eq_zero_or_one y with hye | hyo
  · -- `y` even, so `x` and `z'` are odd
    have hzo : z' % 2 = 1 := by
      have hxo : x % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one x with h0 | h1
        · exfalso
          have h2x : (2 : ℤ) ∣ x := Int.dvd_of_emod_eq_zero h0
          have h2y : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero hye
          have := Int.dvd_gcd h2x h2y; rw [hcop] at this; norm_num at this
        · exact h1
      have : Odd (z' ^ 2) := by
        rw [← h']
        exact (((Int.odd_iff.mpr hxo).pow).sub_even
          ((Int.even_iff.mpr hye).pow_of_ne_zero (by norm_num)))
      exact Int.odd_iff.mp ((Int.odd_pow.mp this).resolve_right (by norm_num))
    have hpt : PythagoreanTriple z' (y ^ 2) (x ^ 2) := by
      unfold PythagoreanTriple; linear_combination -h'
    obtain ⟨m, n, h1, h2, h3, hmn, hpar, hm0⟩ := PythagoreanTriple.coprime_classification' hpt
      (Int.isCoprime_iff_gcd_eq_one.mp hcopyz.symm) hzo hx2pos
    have hmn0 : 0 < m * n := by
      have : 0 < y ^ 2 := by positivity
      nlinarith
    obtain ⟨u, v, hu, hv, huv, hsum⟩ : ∃ u v : ℤ, u % 2 = 1 ∧ v ≠ 0 ∧ Int.gcd u v = 1 ∧
        m ^ 2 + n ^ 2 = u ^ 4 + 4 * v ^ 4 := by
      rcases hpar with ⟨hme, hno⟩ | ⟨hmo, hne⟩
      · exact splitStep hme hno hmn hmn0 (by rw [h2])
      · obtain ⟨u, v, a, b, c, d⟩ := splitStep hne hmo (by rwa [Int.gcd_comm])
          (by rwa [mul_comm]) (y := y) (by rw [h2]; ring)
        exact ⟨u, v, a, b, c, by rw [← d]; ring⟩
    obtain ⟨M, N, R, hN, hR, hMNR, hlt⟩ := sumStep huv hu hv (z := x) (by rw [← hsum, h3])
    exact ih M.natAbs (by rw [← hk]; exact Int.natAbs_lt_iff_sq_lt.mpr hlt) M N R rfl hN hR hMNR
  · -- `y` odd
    have hy2o : y ^ 2 % 2 = 1 := Int.odd_iff.mp ((Int.odd_iff.mpr hyo).pow)
    have hpt : PythagoreanTriple (y ^ 2) z' (x ^ 2) := by
      unfold PythagoreanTriple; linear_combination -h'
    obtain ⟨m, n, h1, h2, h3, hmn, -, hm0⟩ := PythagoreanTriple.coprime_classification' hpt
      (Int.isCoprime_iff_gcd_eq_one.mp hcopyz) hy2o hx2pos
    have hn : n ≠ 0 := by rintro rfl; simp at h2; exact hz' h2
    refine ih m.natAbs ?_ m n (x * y) rfl hn (mul_ne_zero hx' hy') ?_
    · rw [← hk, Int.natAbs_lt_iff_sq_lt]
      have : 0 < n ^ 2 := by positivity
      have h3' : x ^ 2 = m ^ 2 + n ^ 2 := h3
      linarith
    · have : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
      rw [this, h1, h3]; ring

/-- **Known result** (Fermat/Euler; equivalent to the previous theorem by the descent above):
`X⁴ + 4Y⁴ = Z²` has no solution in integers with `X ≠ 0` and `Y ≠ 0`. -/
theorem not_fourth_add_four_fourth_eq_sq {X Y Z : ℤ} (hX : X ≠ 0) (hY : Y ≠ 0) :
    X ^ 4 + 4 * Y ^ 4 ≠ Z ^ 2 := by
  intro h
  obtain ⟨g, hg, X, Y, hcop, rfl, rfl⟩ := gcd_reduce (y := Y) hX
  have hg4 : ((g : ℤ) ^ 2) ^ 2 ∣ Z ^ 2 := ⟨X ^ 4 + 4 * Y ^ 4, by rw [← h]; ring⟩
  obtain ⟨Z', rfl⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp hg4
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg
  have h' : X ^ 4 + 4 * Y ^ 4 = Z' ^ 2 := by
    have : (g : ℤ) ^ 4 * (X ^ 4 + 4 * Y ^ 4 - Z' ^ 2) = 0 := by linear_combination h
    have := (mul_eq_zero.mp this).resolve_left (by positivity); linarith
  have hY' : Y ≠ 0 := by rintro rfl; simp at hY
  have hX' : X ≠ 0 := by rintro rfl; simp at hX
  rcases Int.emod_two_eq_zero_or_one X with hXe | hXo
  · obtain ⟨A, rfl⟩ : ∃ A, X = 2 * A := ⟨X / 2, by omega⟩
    have hYo : Y % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one Y with h0 | h1
      · exfalso
        have := Int.dvd_gcd (dvd_mul_right 2 A) (Int.dvd_of_emod_eq_zero h0)
        rw [hcop] at this; norm_num at this
      · exact h1
    have hZe : Even (Z' ^ 2) := ⟨8 * A ^ 4 + 2 * Y ^ 4, by rw [← h']; ring⟩
    obtain ⟨B, rfl⟩ := (Int.even_pow.mp hZe).1
    have hcopYA : Int.gcd Y A = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one] at hcop ⊢; exact hcop.symm.of_mul_right_right
    have hA : A ≠ 0 := by rintro rfl; simp at hX'
    obtain ⟨M, N, R, hN, hR, hMNR, -⟩ := sumStep hcopYA hYo hA (z := B)
      (by have : 4 * (Y ^ 4 + 4 * A ^ 4 - B ^ 2) = 0 := by linear_combination h'
          linarith)
    exact not_fourth_sub_fourth_eq_sq hN hR hMNR
  · obtain ⟨M, N, R, hN, hR, hMNR, -⟩ := sumStep hcop hXo hY' h'
    exact not_fourth_sub_fourth_eq_sq hN hR hMNR

/-- From a point `(x, y)`, `y ≠ 0`, on `y² = x³ − 4ax` one gets `s² = t⁴ + a` with `t ≠ 0`,
via `t = y / (2x)`, `s = x/2 − t²`. -/
private lemma quartic_of_point {a x y : ℚ} (hy : y ≠ 0) (h : y ^ 2 = x ^ 3 - 4 * a * x) :
    ∃ s t : ℚ, t ≠ 0 ∧ s ^ 2 = t ^ 4 + a := by
  have hx : x ≠ 0 := by rintro rfl; simp at h; exact hy h
  refine ⟨x / 2 - (y / (2 * x)) ^ 2, y / (2 * x), by positivity, ?_⟩
  field_simp
  linear_combination (-4 * x ^ 3) * h

/-- **Known result** (Fermat): 2 is not a congruent number. Via `y² = x³ − 4x` and
`s² = t⁴ + 1`, this is Mathlib's `not_fermat_42`. -/
theorem not_isCongruent_two : ¬ IsCongruent 2 := by
  rw [isCongruent_iff_exists_point two_pos]
  rintro ⟨x, y, hy, h⟩
  rw [congruentCurve_nonsingular (by norm_num)] at h
  obtain ⟨s, t, ht, hst⟩ := quartic_of_point (a := 1) hy (by rw [h]; norm_num; ring)
  have hp : t.num ≠ 0 := Rat.num_ne_zero.mpr ht
  have hq : (t.den : ℚ) ≠ 0 := by positivity
  have hv : (s.den : ℚ) ≠ 0 := by positivity
  have key : ((s.num * t.den ^ 2 * s.den : ℤ) : ℚ) ^ 2 =
      ((s.den * t.num : ℤ) : ℚ) ^ 4 + ((s.den * t.den : ℤ) : ℚ) ^ 4 := by
    have e1 : s = s.num / s.den := (Rat.num_div_den s).symm
    have e2 : t = t.num / t.den := (Rat.num_div_den t).symm
    rw [e1, e2] at hst
    push_cast
    field_simp at hst
    linear_combination (s.den : ℚ) ^ 2 * hst
  have key' : (s.den * t.num) ^ 4 + (s.den * t.den : ℤ) ^ 4 = (s.num * t.den ^ 2 * s.den) ^ 2 := by
    exact_mod_cast key.symm
  exact not_fermat_42 (mul_ne_zero (by exact_mod_cast s.den_ne_zero) hp)
    (mul_ne_zero (by exact_mod_cast s.den_ne_zero) (by exact_mod_cast t.den_ne_zero)) key'

/-- **Known result** (Fermat's right-triangle theorem): 1 is not a congruent number, i.e. no
rational right triangle has square area. Via `y² = x³ − x`, `(2s)² = 4t⁴ + 1`, and
`not_fourth_add_four_fourth_eq_sq`. -/
theorem not_isCongruent_one : ¬ IsCongruent 1 := by
  rw [isCongruent_iff_exists_point one_pos]
  rintro ⟨x, y, hy, h⟩
  rw [congruentCurve_nonsingular (by norm_num)] at h
  obtain ⟨s, t, ht, hst⟩ := quartic_of_point (a := 1 / 4) hy (by rw [h]; norm_num; ring)
  have hp : t.num ≠ 0 := Rat.num_ne_zero.mpr ht
  have hq : (t.den : ℚ) ≠ 0 := by positivity
  have hv : (s.den : ℚ) ≠ 0 := by positivity
  have key : ((2 * s.num * t.den ^ 2 * s.den : ℤ) : ℚ) ^ 2 =
      ((s.den * t.den : ℤ) : ℚ) ^ 4 + 4 * ((s.den * t.num : ℤ) : ℚ) ^ 4 := by
    have e1 : s = s.num / s.den := (Rat.num_div_den s).symm
    have e2 : t = t.num / t.den := (Rat.num_div_den t).symm
    rw [e1, e2] at hst
    push_cast
    field_simp at hst
    linear_combination (s.den : ℚ) ^ 2 * hst
  have key' : (s.den * t.den : ℤ) ^ 4 + 4 * (s.den * t.num) ^ 4 =
      (2 * s.num * t.den ^ 2 * s.den) ^ 2 := by
    exact_mod_cast key.symm
  exact not_fourth_add_four_fourth_eq_sq
    (mul_ne_zero (by exact_mod_cast s.den_ne_zero) (by exact_mod_cast t.den_ne_zero))
    (mul_ne_zero (by exact_mod_cast s.den_ne_zero) hp) key'

/-- **Finite check** (not progress on `tunnellConverse` or problem 140): among the squarefree
`1 ≤ n ≤ 15`, Tunnell's criterion holds exactly for `n ∈ {5, 6, 7, 13, 14, 15}`. This is a
statement about `TunnellCriterion` only. These six are proved congruent above, and `1`, `2` are
proved non-congruent; the non-congruence of `3`, `10`, `11` is **not** proved in this file. -/
theorem tunnellCriterion_finite_check :
    ∀ n ∈ Finset.Icc 1 15, Squarefree n →
      (TunnellCriterion n ↔ n ∈ ({5, 6, 7, 13, 14, 15} : Finset ℕ)) := by
  decide +kernel

/-! ## Problem 171: the Morton–Silverman uniform boundedness conjecture -/

/-- `F = (F₀, …, F_N)` defines a **degree-`d` morphism** `ℙᴺ_K → ℙᴺ_K`: the `Fᵢ` are
homogeneous of degree `d` with no common zero in `K̄^{N+1}` other than `0`. -/
def IsMorphismOfDegree {K : Type} [Field K] {N : ℕ} (d : ℕ)
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) : Prop :=
  (∀ i, (F i).IsHomogeneous d) ∧
    ∀ x : Fin (N + 1) → AlgebraicClosure K, (∀ i, MvPolynomial.aeval x (F i) = 0) → x = 0

/-- The map on affine cones `v ↦ (F₀(v), …, F_N(v))`. -/
def coneMap {K : Type} [Field K] {N : ℕ} (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) :
    (Fin (N + 1) → K) → (Fin (N + 1) → K) :=
  fun v i => MvPolynomial.eval v (F i)

/-- The `K`-rational **preperiodic points** of the morphism `[F]`: points `P ∈ ℙᴺ(K)` with
`φᵐ(P) = φⁿ(P)` for some `m < n` (equivalently, finite forward orbit). Equality in `ℙᴺ` is
proportionality of representatives; by homogeneity this does not depend on the chosen
representative `P.rep`. -/
def preperiodicPoints {K : Type} [Field K] {N : ℕ}
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) :
    Set (Projectivization K (Fin (N + 1) → K)) :=
  {P | ∃ m n : ℕ, m < n ∧ ∃ c : K, c ≠ 0 ∧ (coneMap F)^[n] P.rep = c • (coneMap F)^[m] P.rep}

/-- **ProofAtlas problem 171 (Morton–Silverman Uniform Boundedness Conjecture), OPEN (with
solved subcases).**

Quoted `exactTarget`: "For all fixed integers N>=1, d>=2 and D>=1, there exists a finite
constant C(N,d,D) such that for every number field K with [K:Q]<=D and every degree-d
K-morphism phi:P^N_K->P^N_K, the set of K-rational preperiodic points has cardinality at most
C(N,d,D). A point is preperiodic when its forward orbit under phi is finite. The morphism is
everywhere defined, equivalently given by homogeneous degree-d forms with no common projective
zero. The bound is independent of the field and map except for N,d,D; no effective formula or
classification is required."

Modelling choices: number fields are types `K : Type` with `[NumberField K]` (every number
field has a model in `Type`); `[K:ℚ]` is `Module.finrank ℚ K`; the morphism is given by forms
`F : Fin (N+1) → MvPolynomial (Fin (N+1)) K` as in `IsMorphismOfDegree` ("no common
projective zero" is taken over `AlgebraicClosure K`, the standard meaning); `ℙᴺ(K)` is
`Projectivization K (Fin (N+1) → K)`; cardinality is `Set.encard` (so an infinite set violates
the bound). -/
def MortonSilverman : Prop :=
  ∀ N d D : ℕ, 1 ≤ N → 2 ≤ d → 1 ≤ D → ∃ C : ℕ,
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K ≤ D →
      ∀ F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K, IsMorphismOfDegree d F →
        (preperiodicPoints F).encard ≤ C

/-! ## Problem 211: Serre's uniformity question -/

/-- An algebraic closure of `ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

open Classical in
/-- The `p`-torsion subgroup `E[p] ⊆ E(ℚ̄)`. -/
noncomputable def torsionPoints (W : WeierstrassCurve ℚ) (p : ℕ) :
    AddSubgroup (W.toAffine⁄Qbar).Point :=
  (nsmulAddMonoidHom (α := (W.toAffine⁄Qbar).Point) p).ker

/-- The 13 `j`-invariants of elliptic curves over `ℚ` with complex multiplication (over `ℚ̄`). -/
def cmJInvariants : Finset ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000,
    -147197952000, -262537412640768000}

open Classical in
/-- **ProofAtlas problem 211 (Serre Uniformity Question), OPEN.**

Quoted `exactTarget`: "Determine whether there exists a bound N > 0 such that for every non-CM
elliptic curve E over Q and every prime p > N, the residual Galois representation rho_{E,p} on
E[p] is surjective onto GL_2(F_p)."

Modelling choices:
* the Prop is the **affirmative** answer (the expected one); "determine whether" is a yes/no
  question, and its negation `¬ SerreUniformity` is the other answer;
* elliptic curves over `ℚ` are `WeierstrassCurve ℚ` with `IsElliptic`;
* "non-CM" is `W.j ∉ cmJInvariants`: Mathlib has no endomorphism rings of elliptic curves, and
  this uses the known theorem (class number one, Heegner–Baker–Stark; not in Mathlib) that an
  elliptic curve over `ℚ` has CM over `ℚ̄` iff its `j`-invariant is one of these 13 values;
* `E[p]` is `torsionPoints W p ⊆ E(ℚ̄)`; `G_ℚ` is `Qbar ≃ₐ[ℚ] Qbar`, acting through
  `WeierstrassCurve.Affine.Point.map`. Since `E[p] ≅ (ℤ/p)²` (known; not in Mathlib),
  `GL₂(𝔽_p)` is the group of additive automorphisms of `E[p]`, so surjectivity of `ρ_{E,p}`
  is: every additive automorphism of `E[p]` is induced by some `σ ∈ G_ℚ`. -/
def SerreUniformity : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic], W.j ∉ cmJInvariants →
    ∀ p : ℕ, p.Prime → N < p → ∀ φ : torsionPoints W p ≃+ torsionPoints W p,
      ∃ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ P : torsionPoints W p,
        Affine.Point.map (W' := W.toAffine) (σ : Qbar →ₐ[ℚ] Qbar)
          (P : (W.toAffine⁄Qbar).Point) = φ P

end CryptoLean.OpenProblems.NumberTheory.EllipticCurves

open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_iff_exists_point
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_iff_mul_sq
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_five
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_six
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_seven
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_thirteen
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_fourteen
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isCongruent_fifteen
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms not_fourth_sub_fourth_eq_sq
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms not_fourth_add_four_fourth_eq_sq
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms not_isCongruent_one
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms not_isCongruent_two
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms isElliptic_congruentCurve
open CryptoLean.OpenProblems.NumberTheory.EllipticCurves in
#print axioms tunnellCriterion_finite_check
