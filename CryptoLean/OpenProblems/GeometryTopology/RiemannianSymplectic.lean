import Mathlib

/-!
# Riemannian, symplectic and contact geometry; mapping class groups
(ProofAtlas geometry & topology list)

None of the problems below is solved here, and nothing in this file suggests that any of them
is resolved. Two problems about mapping class groups of closed surfaces are stated as unproved
`def … : Prop`s through a purely group-theoretic model (Dehn–Nielsen–Baer, see below); all the
others need objects that Mathlib does not have and are recorded in the table.

## What Mathlib has and lacks (spot-checked in the pinned Mathlib)

Mathlib has smooth manifolds (`Geometry/Manifold`), immersions and smooth embeddings, Riemannian
metrics as bundle metrics with the induced path length and distance
(`Geometry/Manifold/Riemannian/Basic.lean`, `PathELength.lean`), the Euclidean Laplacian on
inner-product spaces, singular homology, `PresentedGroup`, `MulAut`, characteristic and
finite-index subgroups. It also has covariant derivatives on vector bundles
(`Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`, `structure CovariantDerivative`),
their torsion (`Torsion.lean`), metric compatibility (`Metric.lean`) and the **Levi-Civita
connection** (`LeviCivita.lean`: `CovariantDerivative.IsLeviCivitaConnection`, the Koszul
formula, uniqueness, `CovariantDerivative.leviCivitaConnection`); the Euler characteristic of
graded objects and homological complexes (`Algebra/Homology/EulerCharacteristic.lean`,
`eulerChar`); word metrics on groups (`Geometry/Group/WordMetric.lean`); and ends of graphs
(`Combinatorics/SimpleGraph/Ends`). It has **no** Riemann curvature tensor, sectional or
Gaussian curvature (grep finds no curvature tensor anywhere in `Mathlib/Geometry`), covariant
derivative along curves, geodesic equation / exponential map / conjugate points / geodesic flow,
Laplace–Beltrami operator on a manifold or its spectrum, second fundamental form or mean
curvature of a submanifold, differential forms on manifolds (hence no symplectic or contact
forms, Reeb vector fields, Legendrian or Lagrangian submanifolds, Hamiltonian
diffeomorphisms), a ready-made Euler characteristic of a topological space or manifold (one
could be assembled from singular homology with rational coefficients and `eulerChar`, together
with a finiteness proof for closed manifolds, but this is not in Mathlib), mapping class groups
of surfaces (isotopy classes of homeomorphisms), word-hyperbolic groups, a packaged notion of
ends of a finitely generated group (definable via ends of a Cayley graph), the Lie groups
`PU(n,1)` with their lattices (Mathlib does have `MeasureTheory.covolume` and quotient Haar
measures, `MeasureTheory/Measure/Haar/Quotient.lean`, but not these groups), or arithmetic
subgroups of algebraic groups.

## Open problems stated as `Prop`s

| rank | problem | declaration |
|------|---------|-------------|
| 270 | Congruence subgroup property for `Mod(S_g)`, `g ≥ 3` | `CongruenceSubgroupProperty` |

Additional, separately named and clearly labelled **special case** (not the ranked problem):
`IvanovConjectureClosed` is the `n = 0` (closed surface) case of rank 491, which itself stays
in the table below because punctured surfaces are not modelled.

### The group-theoretic model of `Mod(S_g)` (modelling simplification, used by both Props)

* `SurfaceGroup g` is the one-relator presentation
  `⟨a₁, b₁, …, a_g, b_g | [a₁,b₁]⋯[a_g,b_g]⟩` of `π₁(S_g)` (a known theorem: the standard CW
  structure on `S_g`; not formalized here).
* By the **Dehn–Nielsen–Baer theorem** (known, not formalized here), for `g ≥ 1` the extended
  mapping class group `Mod^±(S_g)` is isomorphic to `Out(π₁ S_g)`, and `Mod(S_g)` is its
  index-2 subgroup of orientation-preserving classes. We work with `Out(π₁ S_g)` itself,
  represented without forming a quotient: a subgroup of `Out` is a subgroup of
  `MulAut (SurfaceGroup g)` containing all inner automorphisms (same index), and the
  kernel of `Out(π₁) → Out(π₁/N)` consists of the automorphisms that preserve `N` (automatic
  for characteristic `N`) and induce an inner automorphism of `π₁/N`, i.e. there is `c : π₁`
  with `φ x · (c x c⁻¹)⁻¹ ∈ N` for all `x`.
* Passing from `Mod` to `Mod^± = Out` does not change either statement (known, elementary
  arguments, not formalized here): finite-index subgroups of `Mod` are finite-index in `Out` and
  conversely intersect `Mod` in finite index; for the congruence property one additionally takes
  `N` inside the characteristic subgroup `π₁' · π₁³` (kernel of `π₁ → H₁(S_g; ℤ/3)`), on which
  orientation-reversing classes act anti-symplectically, hence nontrivially (as `-1 ≠ 1` mod 3);
  for Ivanov's property, a surjection `Γ → ℤ` restricts to `Γ ∩ Mod` with image a nonzero,
  hence infinite cyclic, subgroup of `ℤ`.

## Open problems not expressible faithfully with Mathlib today

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 156 | Weinstein conjecture (periodic Reeb orbits on closed contact manifolds) | differential forms on manifolds, contact forms `α` with `α ∧ (dα)ⁿ ≠ 0`, the Reeb vector field of `α` and its flow (integral curves exist in Mathlib, but not the Reeb field) |
| 196 | Hopf conjecture: positive sectional curvature ⇒ `χ > 0` (closed, even-dimensional) | Riemann curvature tensor and sectional curvature (the Levi-Civita connection itself **is** in Mathlib, `CovariantDerivative.leviCivitaConnection`, but no curvature is built from it); a packaged Euler characteristic of a closed manifold (singular homology and `eulerChar` for complexes exist, but finite generation of the homology of a closed manifold and the resulting `χ(M)` are not in Mathlib) |
| 228 | Hopf conjecture: nonnegative sectional curvature ⇒ `χ ≥ 0` | same as 196: sectional curvature; Euler characteristic of a closed manifold |
| 239 | Complex linearity of `Mod(S_g)`, `g ≥ 3`, determined genus by genus | the mapping class group `Mod(S_g)` (isotopy classes of orientation-preserving homeomorphisms; the Dehn–Nielsen–Baer model above would serve, but the problem asks to *determine a set of genera*, which is not a single `Prop`; faithful linearity predicates `∃ n, ∃ ρ : Mod(S_g) →* GL n ℂ, injective` are definable on top of that model) |
| 240 | Michel boundary rigidity conjecture for simple manifolds (`n ≥ 3`) | geodesics and conjugate points (Jacobi fields / exponential map), strict convexity of the boundary (second fundamental form), simple metrics; pull-back of a Riemannian metric by a diffeomorphism of a manifold with boundary as a bundle-metric equality |
| 264 | Marked length spectrum rigidity (negative curvature) | sectional curvature; free homotopy classes of loops with their unique closed geodesic and its length (marked length spectrum); isotopy of diffeomorphisms |
| 269 | Infinitely many closed geodesics on every closed Riemannian manifold (`dim ≥ 2`) | covariant derivative along a curve and hence the geodesic equation `∇_{γ'} γ' = 0` (the Levi-Civita connection exists in Mathlib as `CovariantDerivative.leviCivitaConnection`, but only for vector fields, not along curves), closed geodesics and their geometric distinctness / primitivity (the Riemannian distance alone does not define local geodesics faithfully) |
| 274 | Arnold chord conjecture in dimension `2n+1`, `n ≥ 2` | contact forms and Reeb vector fields (as for 156), Legendrian submanifolds (`α|_Λ = 0`, `dim Λ = n`), co-orientation of the contact distribution |
| 277 | Gromov's surface subgroup question for one-ended hyperbolic groups | word-hyperbolic groups (δ-thin triangles in a Cayley graph / Gromov product; word metrics exist in `Geometry/Group/WordMetric.lean`, hyperbolicity does not); "one-ended" is not packaged for groups but would be definable via ends of a Cayley graph (`Combinatorics/SimpleGraph/Ends`), so the blocking gap is hyperbolicity. Audit note (2026-11-27): this is the row closest to a faithful `Prop`; Mathlib's `gromovProduct` (`Topology/MetricSpace/GromovProduct.lean`) and the word metric give the four-point δ-hyperbolicity condition directly, and `SurfaceGroup` is defined in this file, so a statement is a candidate follow-up |
| 285 | Nirenberg problem on `S²` (characterize prescribable Gaussian curvatures) | Gaussian curvature of a metric on `S²` (equivalently the Laplace–Beltrami operator of the round sphere in `K = e^{-2u}(1 - Δ_{g_round} u)`); moreover the target asks for an exact characterization, not a single `Prop` |
| 301 | Arithmeticity of lattices in `PU(n,1)`, `n ≥ 4` | the Lie group `PU(n,1)` and its lattices (`MeasureTheory.covolume` and quotient Haar measures exist in Mathlib; the group itself does not), arithmetic subgroups (ℚ-forms of algebraic groups, commensurability, compact-kernel projections) |
| 310 | Hopf: no positively curved metric on `S² × S²` | sectional curvature of a Riemannian metric (the manifold `S² × S²` and bundle metrics exist in Mathlib) |
| 333 | Yau's first eigenvalue conjecture for minimal hypersurfaces of `S^{n+1}` | mean curvature / minimality of an embedded hypersurface of the sphere, Laplace–Beltrami operator of the induced metric and its spectrum |
| 338 | Arnold–Givental Lagrangian intersection conjecture | symplectic forms, anti-symplectic involutions, Hamiltonian diffeomorphisms (time-1 maps of Hamiltonian isotopies), transversality of submanifolds, ℤ/2 Betti numbers of a manifold (ℤ/2 singular homology exists, but not its total dimension as a manifold invariant) |
| 447 | Strong Chern conjecture (constant scalar curvature minimal hypersurfaces of the sphere are isoparametric) | mean curvature, scalar curvature of the induced metric, principal curvatures (isoparametric = constant principal curvatures) |
| 456 | Symplectic isotopy conjecture in `ℂP²` | the Fubini–Study symplectic form on `ℂP²`, symplectic surfaces, isotopies through symplectic embeddings, complex algebraic curves in `ℂP²` as smooth submanifolds with degree |
| 469 | Klingenberg conjecture on Anosov geodesic flows | geodesic flow on the unit tangent bundle, Anosov (uniformly hyperbolic) flows, sectional curvature |
| 470 | Stable Bernstein problem for `M⁶ ⊂ ℝ⁷` | second fundamental form and mean curvature of an immersed hypersurface (minimality), the induced metric's Laplacian and volume measure (stability inequality `∫ |A|² φ² ≤ ∫ |∇φ|²`), completeness of the induced metric, two-sidedness (unit normal field). The graph case is not a substitute: entire minimal graphs over `ℝ⁶` are hyperplanes by Simons' theorem (1968), a known result. |
| 491 | Ivanov's conjecture (`H₁(Γ;ℚ) = 0`) for `Mod_{g,n}`, `g ≥ 3`, `n ≥ 0` | mapping class groups of **punctured** surfaces (the Dehn–Nielsen–Baer model for `n > 0` needs the peripheral structure of the free group `π₁(S_{g,n})`); only the closed case `n = 0` is stated, as the labelled special case `IvanovConjectureClosed` |

## Known results proved here

* `surfaceGroup_one_commute`: the genus-1 surface group `⟨a, b | [a,b]⟩` (the fundamental
  group of the torus) is commutative — a finite algebraic check of the model.
-/

namespace CryptoLean.OpenProblems.GeometryTopology.RiemannianSymplectic

/-! ## Surface groups -/

/-- The relator `[a₁,b₁]⋯[a_g,b_g]` of the standard presentation of `π₁(S_g)`, with generator
`(i, false) = aᵢ` and `(i, true) = bᵢ`. -/
def surfaceRelator (g : ℕ) : FreeGroup (Fin g × Bool) :=
  (List.ofFn fun i : Fin g =>
    FreeGroup.of (i, false) * FreeGroup.of (i, true) * (FreeGroup.of (i, false))⁻¹ *
      (FreeGroup.of (i, true))⁻¹).prod

/-- The fundamental group `π₁(S_g)` of the closed orientable surface of genus `g`, by its
standard one-relator presentation. -/
abbrev SurfaceGroup (g : ℕ) : Type := PresentedGroup ({surfaceRelator g} : Set _)

/-- Inner automorphisms of `G`, as a subgroup of `MulAut G`. -/
def innerAut (G : Type*) [Group G] : Subgroup (MulAut G) := (MulAut.conj (G := G)).range

/-- `φ ∈ Aut(G)` lies in the kernel of `Out(G) → Out(G/N)` (for `N` characteristic): the
automorphism of `G/N` induced by `φ` is inner. -/
def InducesInnerMod {G : Type*} [Group G] (N : Subgroup G) (φ : MulAut G) : Prop :=
  ∃ c : G, ∀ x : G, φ x * (c * x * c⁻¹)⁻¹ ∈ N

/-- **Open problem (ProofAtlas rank 270), congruence subgroup property for mapping class
groups.** Not proved here.

ProofAtlas exactTarget (quoted): "For every closed connected orientable surface S of genus g≥3
and every finite-index subgroup H of its orientation-preserving mapping class group Mod(S),
there exists a finite-index characteristic subgroup N of π1(S) such that
ker(Mod(S)→Out(π1(S)/N)) is contained in H."

Modelling simplifications (see the module comment):
* `π₁(S_g)` is the standard one-relator group `SurfaceGroup g`;
* `Mod(S_g)` is replaced by `Mod^±(S_g) ≅ Out(π₁ S_g)` (Dehn–Nielsen–Baer), and a subgroup of
  `Out` by a subgroup of `MulAut` containing the inner automorphisms; the two statements are
  equivalent by the elementary argument in the module comment (not formalized);
* `ker(Out(π₁) → Out(π₁/N))` is expressed by `InducesInnerMod N`. -/
def CongruenceSubgroupProperty : Prop :=
  ∀ g : ℕ, 3 ≤ g → ∀ H : Subgroup (MulAut (SurfaceGroup g)),
    innerAut (SurfaceGroup g) ≤ H → H.FiniteIndex →
      ∃ N : Subgroup (SurfaceGroup g), N.Characteristic ∧ N.FiniteIndex ∧
        ∀ φ : MulAut (SurfaceGroup g), InducesInnerMod N φ → φ ∈ H

/-- **Open problem, special case `n = 0` of ProofAtlas rank 491 (Ivanov's conjecture)** —
a separately named, clearly labelled special case; it is *not* the ranked problem, which also
covers punctured surfaces (`n ≥ 1`) and is recorded in the table. Not proved here.

ProofAtlas exactTarget of rank 491 (quoted): "For every closed connected orientable surface of
genus g≥3 with n≥0 punctures, and every finite-index subgroup Γ of its orientation-preserving
mapping class group Mod_(g,n), prove H_1(Γ;Q)=0, equivalently that Γ has no surjection onto
Z."

This Prop: only `n = 0`; uses the "no surjection onto ℤ" formulation; `Mod(S_g)` is replaced
by `Out(π₁ S_g)` exactly as in `CongruenceSubgroupProperty` (Dehn–Nielsen–Baer, plus the
restriction argument in the module comment). A finite-index subgroup `Γ` of `Out` is a
finite-index subgroup of `MulAut` containing the inner automorphisms, and a homomorphism
`Γ → ℤ` from `Γ ≤ Out` is a homomorphism from its preimage killing the inner automorphisms. -/
def IvanovConjectureClosed : Prop :=
  ∀ g : ℕ, 3 ≤ g → ∀ Γ : Subgroup (MulAut (SurfaceGroup g)),
    ∀ hΓ : innerAut (SurfaceGroup g) ≤ Γ, Γ.FiniteIndex →
      ∀ f : Γ →* Multiplicative ℤ,
        (∀ φ (hφ : φ ∈ innerAut (SurfaceGroup g)), f ⟨φ, hΓ hφ⟩ = 1) →
          ¬ Function.Surjective f

/-! ## Known result (finite algebraic check of the model) -/

/-- **Known result** (the fundamental group of the torus is `ℤ²`, in particular abelian; see
e.g. Hatcher, *Algebraic Topology*, Example 1.20/§1.2): the genus-1 surface group
`⟨a, b | [a,b]⟩` is commutative. -/
theorem surfaceGroup_one_commute (x y : SurfaceGroup 1) : x * y = y * x := by
  have hgen : ∀ u v : Fin 1 × Bool,
      (PresentedGroup.of u : SurfaceGroup 1) * PresentedGroup.of v =
        PresentedGroup.of v * PresentedGroup.of u := by
    have hrel : (PresentedGroup.of ((0 : Fin 1), false) : SurfaceGroup 1) *
        PresentedGroup.of ((0 : Fin 1), true) =
        PresentedGroup.of ((0 : Fin 1), true) * PresentedGroup.of ((0 : Fin 1), false) := by
      have e : surfaceRelator 1 = FreeGroup.of ((0 : Fin 1), false) *
          FreeGroup.of ((0 : Fin 1), true) * (FreeGroup.of ((0 : Fin 1), false))⁻¹ *
          (FreeGroup.of ((0 : Fin 1), true))⁻¹ := by
        simp [surfaceRelator]
      have h1 : PresentedGroup.mk ({surfaceRelator 1} : Set _)
          (FreeGroup.of ((0 : Fin 1), false) * FreeGroup.of ((0 : Fin 1), true) *
            (FreeGroup.of ((0 : Fin 1), false))⁻¹ * (FreeGroup.of ((0 : Fin 1), true))⁻¹) = 1 := by
        calc _ = PresentedGroup.mk ({surfaceRelator 1} : Set _) (surfaceRelator 1) := by rw [e]
          _ = 1 := PresentedGroup.one_of_mem (Set.mem_singleton _)
      simp only [map_mul, map_inv] at h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    rintro ⟨i, a⟩ ⟨j, b⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    cases a <;> cases b
    · rfl
    · exact hrel
    · exact hrel.symm
    · rfl
  have hall : ∀ u : Fin 1 × Bool, ∀ z : SurfaceGroup 1,
      PresentedGroup.of u * z = z * PresentedGroup.of u := by
    intro u z
    have hz : z ∈ Subgroup.centralizer {(PresentedGroup.of u : SurfaceGroup 1)} := by
      have : Subgroup.closure (Set.range (PresentedGroup.of (rels := ({surfaceRelator 1} :
          Set _)))) ≤ Subgroup.centralizer {PresentedGroup.of u} := by
        rw [Subgroup.closure_le]
        rintro _ ⟨v, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact (hgen u v).symm
      rw [PresentedGroup.closure_range_of] at this
      exact this (Subgroup.mem_top _)
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    exact hz.symm
  have hx : x ∈ Subgroup.centralizer {y} := by
    have : Subgroup.closure (Set.range (PresentedGroup.of (rels := ({surfaceRelator 1} :
        Set _)))) ≤ Subgroup.centralizer {y} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hall v y)
    rw [PresentedGroup.closure_range_of] at this
    exact this (Subgroup.mem_top _)
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  exact hx

end CryptoLean.OpenProblems.GeometryTopology.RiemannianSymplectic

#print axioms CryptoLean.OpenProblems.GeometryTopology.RiemannianSymplectic.surfaceGroup_one_commute
