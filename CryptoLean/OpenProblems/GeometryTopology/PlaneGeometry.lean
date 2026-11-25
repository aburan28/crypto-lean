import Mathlib

/-!
# Open problems in geometry: square peg, Pansu, Kelvin, filling area, Hilbert's third

ProofAtlas release ranks 329, 330, 423, 448, 490.

All problems in this file are **open**. Nothing here resolves, or claims to resolve,
any of them. Open problems that admit a faithful statement over Mathlib appear as
unproved `def … : Prop`; the others are listed in the table below together with the
Mathlib objects whose absence prevents a faithful statement.

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 329 | Hilbert's third problem for spherical and hyperbolic scissors congruence (is volume injective on the kernel of the Dehn invariant for `S^3` and `H^3`?) | hyperbolic 3-space `H^3` as a model geometry with its isometry group and hyperbolic volume; geodesic polyhedra in `S^3` / `H^3` and their dihedral angles; scissors-congruence groups `P(X)` (polytope groups modulo cutting and isometry); the Dehn invariant `P(X) → ℝ ⊗_ℤ ℝ/πℤ` |
| 490 | Kelvin problem (least perimeter-density partition of `ℝ^3` into unit-volume cells; optimality of the Weaire–Phelan structure) | the Weaire–Phelan foam (an explicit periodic partition with curved, constant-mean-curvature faces) and the Kelvin foam as Mathlib objects; De Giorgi sets of finite perimeter / reduced boundary and the perimeter-density functional of an infinite cluster (only the crude substitute `μH[2]` of topological frontiers is available, and the problem's "determine the optimal partition" part is not a proposition) |

The three faithfully stated problems are

* rank 423, the square peg problem: `SquarePegConjecture`;
* rank 448, Pansu's isoperimetric conjecture in the first Heisenberg group:
  `PansuIsoperimetricConjecture`;
* rank 330, Gromov's filling area conjecture: `GromovFillingAreaConjecture` (stated with
  Mathlib's Riemannian manifolds over the half-space model `𝓡∂ 2`, an oriented-atlas
  definition `IsOrientableManifold` of orientability, which Mathlib lacks, and the
  normalised Hausdorff measure `μHE[2]` of the Riemannian distance as area).

Proved results (all *known*, elementary):

* `circleCurve_isJordanCurve`, `circle_hasInscribedSquare`: every round circle in the
  plane is a Jordan curve with an inscribed square (classical, trivial case of the
  square peg problem);
* `IsSquare.vertices_distinct`: the square predicate is nondegenerate;
* `hmul_X`, `hmul_Y`, `dil_hmul`, `hmul_assoc`: algebraic sanity checks of the Heisenberg
  group model used for rank 448 (the horizontal fields are the left-invariant fields of
  the group law, the dilations are group automorphisms, the law is associative).
-/

namespace CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry

open MeasureTheory Complex Set Bundle
open scoped Manifold ContDiff
open scoped ENNReal

/-! ## Rank 423: the square peg problem -/

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- `a, b, c, d` (in cyclic order) are the vertices of a nondegenerate square:
four equal sides, equal diagonals, and `a ≠ c`.  In the plane, a quadrilateral with four
equal sides and equal, nonzero diagonals is exactly a square. -/
def IsSquare (a b c d : Plane) : Prop :=
  a ≠ c ∧ dist a b = dist b c ∧ dist b c = dist c d ∧ dist c d = dist d a ∧
    dist a c = dist b d

/-- A Jordan curve (continuous simple closed curve) in the plane: a continuous injective map
from the circle `ℝ/ℤ` into `ℝ²`. -/
def IsJordanCurve (γ : AddCircle (1 : ℝ) → Plane) : Prop :=
  Continuous γ ∧ Function.Injective γ

/-- The curve `γ` has an inscribed square: four points of its image are the vertices of a
nondegenerate square. -/
def HasInscribedSquare (γ : AddCircle (1 : ℝ) → Plane) : Prop :=
  ∃ a b c d : Plane, a ∈ Set.range γ ∧ b ∈ Set.range γ ∧ c ∈ Set.range γ ∧
    d ∈ Set.range γ ∧ IsSquare a b c d

/-- **Open problem (ProofAtlas rank 423, Square Peg Problem / Toeplitz's inscribed square
conjecture).**

ProofAtlas exactTarget: "Prove or disprove that every continuous simple closed (Jordan)
curve in the plane contains four points forming the vertices of a square."

Status: open (with solved subcases, e.g. smooth, piecewise analytic, locally monotone
curves). The proposition below is the conjecture; proving either it or its negation would
resolve the problem.

Modelling choices: a Jordan curve is a continuous injective map `ℝ/ℤ → ℝ²`
(`AddCircle 1 → EuclideanSpace ℝ (Fin 2)`), i.e. a parametrised simple closed curve; "four
points forming a square" is `IsSquare` (four equal sides and two equal nonzero diagonals,
which in the plane characterises nondegenerate squares). -/
def SquarePegConjecture : Prop :=
  ∀ γ : AddCircle (1 : ℝ) → Plane, IsJordanCurve γ → HasInscribedSquare γ

/-- The vertices of an `IsSquare` are pairwise distinct (sanity check: the predicate is
nondegenerate). -/
theorem IsSquare.vertices_distinct {a b c d : Plane} (h : IsSquare a b c d) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨hac, h1, h2, h3, h4⟩ := h
  have hac' : 0 < dist a c := dist_pos.2 hac
  have hbd : 0 < dist b d := h4 ▸ hac'
  have hab : 0 < dist a b := by
    by_contra hn
    push Not at hn
    have : dist a c ≤ dist a b + dist b c := dist_triangle a b c
    linarith [dist_nonneg (x := a) (y := b)]
  have hda : 0 < dist d a := by linarith
  exact ⟨dist_pos.1 hab, hac, fun e => dist_pos.1 hda e.symm, dist_pos.1 (by linarith),
    dist_pos.1 hbd, dist_pos.1 (by linarith)⟩

/-- The round circle of center `c` and radius `r`, parametrised by `ℝ/ℤ`. -/
noncomputable def circleCurve (c : Plane) (r : ℝ) (t : AddCircle (1 : ℝ)) : Plane :=
  c + r • Complex.orthonormalBasisOneI.repr
    ((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) t : Circle) : ℂ)

/-- **Known result** (classical): a round circle of positive radius is a Jordan curve. -/
theorem circleCurve_isJordanCurve (c : Plane) {r : ℝ} (hr : 0 < r) :
    IsJordanCurve (circleCurve c r) := by
  refine ⟨?_, ?_⟩
  · unfold circleCurve
    have h1 := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).continuous
    have h2 := Complex.orthonormalBasisOneI.repr.continuous
    fun_prop
  · intro s t h
    unfold circleCurve at h
    have h' := smul_right_injective Plane hr.ne' (add_left_cancel h)
    exact (AddCircle.homeomorphCircle _).injective
      (Circle.coe_injective (Complex.orthonormalBasisOneI.repr.injective h'))

lemma mem_range_circleCurve (c : Plane) (r : ℝ) (z : ℂ) (hz : ‖z‖ = 1) :
    c + r • Complex.orthonormalBasisOneI.repr z ∈ Set.range (circleCurve c r) := by
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).surjective
    ⟨z, mem_sphere_zero_iff_norm.2 hz⟩
  exact ⟨t, by simp [circleCurve, ht]⟩

/-- **Known result** (classical; the trivial case of the square peg problem): every round
circle of positive radius in the plane has an inscribed square, namely the points at
angles `0, π/2, π, 3π/2`. -/
theorem circle_hasInscribedSquare (c : Plane) {r : ℝ} (hr : 0 < r) :
    IsJordanCurve (circleCurve c r) ∧ HasInscribedSquare (circleCurve c r) := by
  refine ⟨circleCurve_isJordanCurve c hr, ?_⟩
  set R := Complex.orthonormalBasisOneI.repr
  have hd : ∀ z w : ℂ, dist (c + r • R z) (c + r • R w) = r * dist z w := by
    intro z w
    rw [dist_add_left, dist_smul₀, R.dist_map, Real.norm_of_nonneg hr.le]
  refine ⟨c + r • R 1, c + r • R I, c + r • R (-1), c + r • R (-I),
    mem_range_circleCurve c r 1 (by simp), mem_range_circleCurve c r I (by simp),
    mem_range_circleCurve c r (-1) (by simp), mem_range_circleCurve c r (-I) (by simp), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun x => dist x (c + r • R (-1))) h
    simp only [dist_self, hd] at this
    have h2 : dist (1 : ℂ) (-1) = 2 := by
      rw [Complex.dist_eq]; norm_num
    rw [h2] at this; nlinarith
  all_goals
    simp only [hd]
    congr 1
    simp only [Complex.dist_eq, Complex.norm_eq_sqrt_sq_add_sq]
    norm_num

/-! ## Rank 448: Pansu's isoperimetric conjecture in the first Heisenberg group -/

/-- The first Heisenberg group `H¹`, modelled on `ℝ × ℝ × ℝ` with coordinates `(x, y, t)`. -/
abbrev H1 := ℝ × ℝ × ℝ

/-- Group law of `H¹`: `(x,y,t)·(x',y',t') = (x+x', y+y', t+t' + x'y - xy')`. -/
def hmul (p q : H1) : H1 :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2 + (q.1 * p.2.1 - p.1 * q.2.1))

/-- Anisotropic dilation `δ_s(x,y,t) = (sx, sy, s²t)`. -/
def dil (s : ℝ) (p : H1) : H1 := (s * p.1, s * p.2.1, s ^ 2 * p.2.2)

/-- The left-invariant horizontal field `X = ∂ₓ + y ∂ₜ`, as a vector at `p`. -/
def Xvec (p : H1) : H1 := (1, 0, p.2.1)

/-- The left-invariant horizontal field `Y = ∂ᵧ - x ∂ₜ`, as a vector at `p`. -/
def Yvec (p : H1) : H1 := (0, 1, -p.1)

/-- Horizontal divergence `X φ₁ + Y φ₂` of a horizontal vector field `φ = (φ₁, φ₂)`. -/
noncomputable def horizDiv (φ : H1 → ℝ × ℝ) (p : H1) : ℝ :=
  fderiv ℝ (fun q => (φ q).1) p (Xvec p) + fderiv ℝ (fun q => (φ q).2) p (Yvec p)

/-- Test fields for the horizontal perimeter: `C¹`, compactly supported, pointwise norm `≤ 1`. -/
def AdmissibleField (φ : H1 → ℝ × ℝ) : Prop :=
  ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ ∀ p, (φ p).1 ^ 2 + (φ p).2 ^ 2 ≤ 1

/-- Horizontal (De Giorgi / Garofalo–Nhieu) perimeter of `E ⊆ H¹`:
`P_H(E) = sup { ∫_E (X φ₁ + Y φ₂) dℒ³ : φ ∈ C¹_c(H¹, ℝ²), |φ| ≤ 1 }`. -/
noncomputable def horizPerimeter (E : Set H1) : ℝ≥0∞ :=
  ⨆ (φ : H1 → ℝ × ℝ) (_ : AdmissibleField φ), ENNReal.ofReal (∫ p in E, horizDiv φ p)

/-- The region enclosed by the unit Pansu sphere:
`{ r ≤ 1, |t| ≤ (arccos r + r √(1 - r²)) / 2 }` with `r = √(x² + y²)`.
(For the fields `X = ∂ₓ + y∂ₜ`, `Y = ∂ᵧ - x∂ₜ` the Pansu sphere is the union of the
horizontal geodesics, projecting to circles of radius `1/2` through the origin, joining the
poles `(0, 0, ±π/4)`.)

Source of the profile: the Pansu sphere is the union of the horizontal (Carnot–Carathéodory)
geodesics through a pole (P. Pansu, *Une inégalité isopérimétrique sur le groupe de
Heisenberg*, C. R. Acad. Sci. Paris 295 (1982); explicit profile in M. Ritoré and C. Rosales,
*Area-stationary surfaces in the Heisenberg group `H¹`*, Adv. Math. 219 (2008)). Check of the
normalisation used here: the contact form is `dt - y dx + x dy`, so along a horizontal curve
`t' = -2·(swept signed area rate)`; geodesics from the pole project to circles of radius `1/2`
through the origin; writing `r = sin α`, the height is `t = π/4 - (α - sin α cos α)/2`, which
is the stated bound `(arccos r + r √(1 - r²))/2` (re-derived independently by an audit). -/
noncomputable def pansuRegion : Set H1 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 ≤ 1 ∧
    |p.2.2| ≤ (Real.arccos (√(p.1 ^ 2 + p.2.1 ^ 2)) +
      √(p.1 ^ 2 + p.2.1 ^ 2) * √(1 - (p.1 ^ 2 + p.2.1 ^ 2))) / 2}

/-- **Open problem (ProofAtlas rank 448, Pansu's isoperimetric conjecture in the first
Heisenberg group).**

ProofAtlas exactTarget: "In the standard first Heisenberg group H1 with Haar volume and
horizontal perimeter, are the finite-perimeter minimizers of perimeter at each fixed
positive finite volume exactly, up to null sets and left translation, the dilates of the
region enclosed by a Pansu sphere?"

Status: open (with solved subcases: e.g. among sets with symmetry or regularity
assumptions). The proposition below is the affirmative answer; the question is open.

Modelling choices:
* `H¹ = ℝ³` with law `(x,y,t)·(x',y',t') = (x+x', y+y', t+t'+x'y-xy')`; its Haar measure is
  Lebesgue measure `volume` on `ℝ × ℝ × ℝ` (up to a constant factor, irrelevant here);
* horizontal perimeter = De Giorgi-type perimeter `horizPerimeter` w.r.t. the
  left-invariant fields `X = ∂ₓ + y∂ₜ`, `Y = ∂ᵧ - x∂ₜ` (the standard sub-Riemannian
  perimeter of Garofalo–Nhieu / Franchi–Serapioni–Serra Cassano);
* the Pansu region `pansuRegion` is written for these fields, dilations are
  `δ_s(x,y,t) = (sx, sy, s²t)`, left translation by `q` is `p ↦ q·p`;
* "finite-perimeter minimizer at volume `v`" = measurable `E` with `|E| = v`,
  `P_H(E) < ∞` and `P_H(E) ≤ P_H(F)` for every measurable `F` with `|F| = v`;
* "exactly the dilates up to null sets and left translation" = the biconditional with
  `|E Δ q·δ_s(B)| = 0` for some `q` and `s > 0`. The direction "translated dilate of the
  Pansu region ⇒ minimiser" uses that minimisers exist at every volume (a known theorem:
  G. P. Leonardi and S. Rigot, *Isoperimetric sets on Carnot groups*, Houston J. Math. 29
  (2003)); with that, the biconditional is exactly the conjecture. -/
def PansuIsoperimetricConjecture : Prop :=
  ∀ v : ℝ, 0 < v → ∀ E : Set H1, MeasurableSet E → volume E = ENNReal.ofReal v →
    horizPerimeter E < ⊤ →
    ((∀ F : Set H1, MeasurableSet F → volume F = ENNReal.ofReal v →
        horizPerimeter E ≤ horizPerimeter F) ↔
      ∃ (q : H1) (s : ℝ), 0 < s ∧
        volume (symmDiff E ((fun p => hmul q (dil s p)) '' pansuRegion)) = 0)

/-- Finite check (algebraic identity): `X` is the left-invariant field generated by `∂ₓ`,
i.e. `p · (s, 0, 0) = p + s • X(p)`. -/
theorem hmul_X (p : H1) (s : ℝ) : hmul p (s, 0, 0) = p + s • Xvec p := by
  obtain ⟨x, y, t⟩ := p
  simp only [hmul, Xvec, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Finite check (algebraic identity): `Y` is the left-invariant field generated by `∂ᵧ`,
i.e. `p · (0, s, 0) = p + s • Y(p)`. -/
theorem hmul_Y (p : H1) (s : ℝ) : hmul p (0, s, 0) = p + s • Yvec p := by
  obtain ⟨x, y, t⟩ := p
  simp only [hmul, Yvec, Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Finite check (algebraic identity): dilations are group homomorphisms of `H¹`. -/
theorem dil_hmul (s : ℝ) (p q : H1) : dil s (hmul p q) = hmul (dil s p) (dil s q) := by
  obtain ⟨x, y, t⟩ := p
  obtain ⟨x', y', t'⟩ := q
  simp only [hmul, dil, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- Finite check (algebraic identity): the group law of `H¹` is associative. -/
theorem hmul_assoc (p q r : H1) : hmul (hmul p q) r = hmul p (hmul q r) := by
  obtain ⟨x, y, t⟩ := p
  obtain ⟨x', y', t'⟩ := q
  obtain ⟨x'', y'', t''⟩ := r
  simp only [hmul, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-! ## Rank 330: Gromov's filling area conjecture -/

/-- Orientability of an `n`-manifold with boundary modelled on the half-space
`EuclideanHalfSpace n` (Mathlib has no notion of orientable manifold): there is an atlas of
charts from the maximal `C^∞` atlas, covering `M`, all of whose transition maps
`I ∘ e' ∘ e⁻¹ ∘ I⁻¹` have positive Jacobian determinant (derivative within the half-space
`range I`, which is the one-sided derivative at boundary points) at every point of overlap.
This is the standard oriented-atlas definition. -/
def IsOrientableManifold (n : ℕ) [NeZero n] (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] : Prop :=
  ∃ A : Set (OpenPartialHomeomorph M (EuclideanHalfSpace n)),
    A ⊆ IsManifold.maximalAtlas (𝓡∂ n) ∞ M ∧ (∀ x : M, ∃ e ∈ A, x ∈ e.source) ∧
    ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source,
      0 < (fderivWithin ℝ ((𝓡∂ n) ∘ e' ∘ e.symm ∘ (𝓡∂ n).symm) (range (𝓡∂ n))
        ((𝓡∂ n) (e x))).det

/-- **Open problem (ProofAtlas rank 330, Gromov's filling area conjecture).**

ProofAtlas exactTarget: "For every compact orientable Riemannian surface M whose boundary is
isometric to a circle C of circumference 2π and satisfies d_M(x,y)=d_C(x,y) for all x,y in C,
prove Area(M) is at least 2π."

Status: open (with solved subcases, e.g. Pu/Gromov for fillings by discs with the boundary
condition, Bangert–Croke–Ivanov–Katz for genus one). The proposition below is the conjecture.

Modelling choices:
* a compact Riemannian surface with boundary is a compact type `M` that is a `C^∞` manifold
  over the half-space model `𝓡∂ 2 = modelWithCornersEuclideanHalfSpace 2`, with a smooth
  (`IsContMDiffRiemannianBundle … ∞`) Riemannian metric on its tangent bundle, and whose
  extended distance is the Riemannian (path-length) distance (`IsRiemannianManifold`);
  manifolds are quantified over `Type` (every surface has a model there);
* orientability is `IsOrientableManifold 2 M` (oriented atlas; defined above since Mathlib
  lacks it);
* `d_M` is the Riemannian distance `edist` of `M` (intrinsic distance of the whole surface,
  not of the boundary); `C` is `AddCircle (2π)` with its quotient metric, which is the arc
  length distance on a circle of circumference `2π`; "the boundary is the circle `C` with
  `d_M = d_C` on it" is an injective `f : C → M` with image the manifold boundary
  `(𝓡∂ 2).boundary M` and `d_M(f s, f t) = d_C(s, t)`;
* `Area(M)` is `μHE[2] M`, the 2-dimensional Hausdorff measure of the Riemannian distance
  normalised to agree with Lebesgue measure on `ℝ²` (Mathlib has no Riemannian volume
  measure). For a smooth Riemannian surface this equals the Riemannian area by the area
  formula (a known theorem not in Mathlib); the identification is a modelling assumption. -/
def GromovFillingAreaConjecture : Prop :=
  ∀ (M : Type) [EMetricSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (𝓡∂ 2) ∞ M] [CompactSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 2) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ 2) ∞ (EuclideanSpace ℝ (Fin 2))
      (fun x : M ↦ TangentSpace (𝓡∂ 2) x)]
    [IsRiemannianManifold (𝓡∂ 2) M] [MeasurableSpace M] [BorelSpace M],
    IsOrientableManifold 2 M →
    ∀ f : AddCircle (2 * Real.pi) → M, Function.Injective f →
      range f = (𝓡∂ 2).boundary M →
      (∀ s t, edist (f s) (f t) = edist s t) →
      ENNReal.ofReal (2 * Real.pi) ≤ (μHE[2] : Measure M) univ

end CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry

#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.circle_hasInscribedSquare
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.circleCurve_isJordanCurve
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.IsSquare.vertices_distinct
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.hmul_X
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.hmul_Y
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.dil_hmul
#print axioms CryptoLean.OpenProblems.GeometryTopology.PlaneGeometry.hmul_assoc
