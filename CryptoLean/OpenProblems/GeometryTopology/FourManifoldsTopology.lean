import Mathlib

/-!
# Four-manifolds, curvature and homotopy theory: open problems (ProofAtlas geometry & topology)

None of the problems below is solved here, and nothing in this file suggests that any of them
is resolved. Problems whose objects Mathlib already has are stated as unproved `def … : Prop`s,
each with the ProofAtlas `exactTarget` quoted in its docstring and every modelling choice listed.
The others are recorded in the second table, which names exactly what Mathlib lacks.

## Mathlib objects reused

* smooth manifolds: `ChartedSpace`, `IsManifold (𝓡 n) ∞`, diffeomorphisms `M ≃ₘ^∞⟮I, J⟯ N`,
  smooth embeddings `Manifold.IsSmoothEmbedding`, the smooth (analytic) structure on the unit
  sphere `sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`;
* homotopy theory: `ContinuousMap.HomotopyEquiv`, higher homotopy groups `π_ n X x` with their
  commutative group structure for `n ≥ 2`, `SimplyConnectedSpace`, classical CW complexes
  `Topology.CWComplex` and `Topology.RelCWComplex.Finite`;
* singular homology `AlgebraicTopology.singularHomologyFunctor` with coefficients in
  `ModuleCat ℚ` (used for the Euler characteristic);
* structure groupoids: `Pregroupoid`, `Pregroupoid.groupoid`, `HasGroupoid` (used for affine
  manifolds, i.e. atlases whose transition maps are locally affine);
* the Coxeter matrix `CoxeterMatrix.E₈` (used for the `E₈` Gram matrix).

## Open problems stated as `Prop`s

| rank | problem | declaration |
|------|---------|-------------|
| 21  | Smooth four-dimensional Poincaré conjecture | `SmoothPoincare4` |
| 149 | Smooth four-dimensional Schoenflies problem | `SmoothSchoenflies4` |
| 426 | Chern conjecture on the Euler characteristic of closed affine manifolds | `ChernAffineEuler` |
| 444 | Moore's conjecture on homotopy exponents and rational ellipticity | `MooreConjecture` |
| 492 | Markus conjecture on completeness of compact unimodular affine manifolds | `MarkusConjecture` |

## Open problems not expressible faithfully with Mathlib today

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 53  | Novikov conjecture (homotopy invariance of higher signatures) | Hirzebruch `L`-class (Pontryagin classes of the tangent bundle, characteristic classes in rational cohomology), singular cohomology ring with cup product, fundamental class `[M]` of a closed oriented manifold and orientations, a topological classifying space `Bπ₁(M)` with its classifying map `M → Bπ₁(M)` (Mathlib has only the simplicial object `classifyingSpaceUniversalCover` (`EG`) in `RepresentationTheory/Homological/Resolution.lean`, not a topological `Bπ` with a classifying map) |
| 213 | 11/8-conjecture for smooth closed spin 4-manifolds | spin structures (`w₂ = 0`) on smooth manifolds, the intersection form on `H²(M;ℤ)` (cup product, fundamental class / Poincaré duality), hence `b₂(M)` and the signature `σ(M)` as invariants of a manifold; Rokhlin's, Donaldson's and Furuta's theorems are not formalized |
| 299 | Bott conjecture (nonnegatively curved ⇒ rationally elliptic) | Riemann curvature tensor and sectional curvature of a Riemannian metric (no curvature tensor in `Mathlib/Geometry/Manifold`). The other ingredients exist: the based loop space `Ω` (`LoopSpace`, `Path x x` with the compact-open-induced topology, `Mathlib/Topology/Homotopy/HomotopyGroup.lean`) and its Betti numbers over a field `k` via `AlgebraicTopology.singularHomologyFunctor (ModuleCat k)`, and rational ellipticity via `π_ n` (as in `IsRationallyElliptic` below); only the curvature hypothesis is missing |
| 317 | Gromov–Lawson–Rosenberg conjecture, finite fundamental groups | scalar curvature of a Riemannian metric, spin structures, real reduced group C*-algebra `C*_r(G;ℝ)` and its real K-theory `KO_n`, the Rosenberg index `α(M)` (index of the Mishchenko–Fomenko-twisted Dirac operator) |
| 414 | Stolz conjecture (positive Ricci curvature ⇒ Witten genus 0) | Ricci curvature, spin and string structures (`p₁/2 = 0`), Pontryagin classes, the Witten genus (characteristic power series valued in modular forms) |
| 451 | Gromov's vanishing simplicial volume ⇒ χ = 0 question | the fundamental class of a closed oriented manifold in real singular homology, the `ℓ¹`-norm on singular chains (explicit basis of singular simplices for the categorical chain complex) and the induced seminorm on homology; asphericity and `χ` alone are expressible |
| 460 | Geometric simple connectivity of closed simply connected smooth 4-manifolds | handle decompositions of smooth manifolds (attaching `k`-handles along framed embedded spheres), equivalently Morse functions / Morse theory on smooth manifolds with control of index-1 critical points |

## Known results proved here

* the Gram matrix of the `E₈` root lattice, built from Mathlib's `CoxeterMatrix.E₈`
  (`2` on the diagonal, `-1` for an edge of the Dynkin diagram, `0` otherwise), is symmetric,
  even (every value `xᵀ G x` on `ℤ⁸` is even), positive definite over `ℚ` and unimodular
  (`det = 1`). This is the algebraic side of the 11/8 context: `E₈` is the even unimodular
  positive definite form that a hypothetical smooth closed spin 4-manifold could not carry
  (Rokhlin's theorem, not formalized here); it has rank `8 < 11 = (11/8)·8`.
-/

noncomputable section

namespace CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology

open scoped ContDiff Manifold Topology
open Metric Manifold Filter

/-! ## Spheres -/

/-- The unit sphere `S⁴ ⊆ ℝ⁵`, a smooth manifold modelled on `ℝ⁴` (Mathlib instance). -/
abbrev S4 : Type := sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

/-- The unit sphere `S³ ⊆ ℝ⁴`, a smooth manifold modelled on `ℝ³` (Mathlib instance). -/
abbrev S3 : Type := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The equatorial `S³ ⊆ S⁴`: the points of the unit sphere of `ℝ⁵` with last coordinate `0`. -/
def equator : Set S4 := {x : S4 | (x : EuclideanSpace ℝ (Fin 5)) 4 = 0}

/-! ## Rank 21: smooth 4-dimensional Poincaré conjecture -/

/-- **Open problem (ProofAtlas rank 21): smooth four-dimensional Poincaré conjecture.**

ProofAtlas exact target: "Determine whether every smooth closed 4-manifold homotopy equivalent to
the standard 4-sphere S^4 is diffeomorphic to S^4."

The `Prop` below is the affirmative answer; the problem is open in both directions, and its
negation is equally unproved.

Modelling:
* a smooth closed 4-manifold is a compact Hausdorff space `M` with a `C^∞` atlas modelled on
  `ℝ⁴ = EuclideanSpace ℝ (Fin 4)` with the trivial model with corners `𝓡 4` (so `M` has no
  boundary); second countability is automatic for a compact locally Euclidean space;
* `M` is taken in `Type` (universe `0`); every manifold is homeomorphic to one there;
* "homotopy equivalent" is `ContinuousMap.HomotopyEquiv`;
* the standard `S⁴` is the unit sphere of `ℝ⁵` with Mathlib's smooth structure, and
  "diffeomorphic" is a `C^∞` diffeomorphism `M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ S4`.

Mathlib's `Geometry/Manifold/PoincareConjecture.lean` states the Poincaré conjectures in all
dimensions through `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere`; this local `Prop` is
the dimension-4 smooth case written out directly, and is not derived from that file. -/
def SmoothPoincare4 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M],
    Nonempty (ContinuousMap.HomotopyEquiv M S4) → Nonempty (M ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ S4)

/-! ## Rank 149: smooth 4-dimensional Schoenflies problem -/

/-- **Open problem (ProofAtlas rank 149): smooth four-dimensional Schoenflies problem.**

ProofAtlas exact target: "Determine whether every smooth embedding of S^3 in S^4 is smoothly
unknotted; equivalently, whether each of its two complementary closures is diffeomorphic to the
standard 4-ball B^4."

The `Prop` below is the affirmative answer to the first formulation; the problem is open.

Modelling:
* a smooth embedding `S³ → S⁴` is `Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞ f` (a `C^∞`
  immersion which is a topological embedding), with Mathlib's smooth structures on the unit
  spheres of `ℝ⁴` and `ℝ⁵`;
* "smoothly unknotted" is taken in its standard meaning: some self-diffeomorphism of `S⁴` maps
  the image of `f` onto the equatorial `S³` (`equator`, last coordinate `0`);
* the second ("equivalently") formulation is not used: smooth manifolds with boundary such as
  the complementary closures and `B⁴` are not set up here. The equivalence of the two is a known
  theorem not formalized here (glue the two balls; a diffeomorphism of `S³` extends over `B⁴` by
  Cerf's theorem `Γ₄ = 0`). -/
def SmoothSchoenflies4 : Prop :=
  ∀ f : S3 → S4, IsSmoothEmbedding (𝓡 3) (𝓡 4) ∞ f →
    ∃ φ : S4 ≃ₘ^∞⟮𝓡 4, 𝓡 4⟯ S4, φ '' Set.range f = equator

/-! ## Affine manifolds (ranks 426 and 492) -/

section Affine

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The pregroupoid of maps that are, near every point of their domain, equal to an affine map
`E → E` whose linear part lies in the submonoid `S`. With `S = ⊤` its groupoid is the affine
groupoid (atlases with locally affine transition maps); with `S` the maps of determinant `1` it
is the unimodular affine groupoid. -/
def affinePregroupoid (S : Submonoid (Module.End ℝ E)) : Pregroupoid E where
  property f u := ∀ x ∈ u, ∃ A : E →ᵃ[ℝ] E, A.linear ∈ S ∧ f =ᶠ[𝓝 x] A
  comp := by
    intro f g u v hf hg _ _ _ x hx
    obtain ⟨A, hAS, hA⟩ := hf x hx.1
    obtain ⟨B, hBS, hB⟩ := hg (f x) hx.2
    refine ⟨B.comp A, S.mul_mem hBS hAS, ?_⟩
    have hAc : ContinuousAt A x := (AffineMap.continuous_of_finiteDimensional A).continuousAt
    have hfx : f x = A x := hA.eq_of_nhds
    have h1 : ∀ᶠ y in 𝓝 x, B (A y) = g (A y) := by
      have : Tendsto A (𝓝 x) (𝓝 (f x)) := by rw [hfx]; exact hAc
      exact (this.eventually hB).mono fun y hy => hy.symm
    filter_upwards [hA, h1] with y hy1 hy2
    simp [Function.comp, hy1, hy2]
  id_mem := fun _ _ => ⟨AffineMap.id ℝ E, S.one_mem, Eventually.of_forall fun _ => rfl⟩
  locality := by
    intro f u _ h x hx
    obtain ⟨v, _, hxv, hp⟩ := h x hx
    exact hp x ⟨hx, hxv⟩
  congr := by
    intro f g u hu hfg hf x hx
    obtain ⟨A, hAS, hA⟩ := hf x hx
    refine ⟨A, hAS, ?_⟩
    filter_upwards [hA, hu.mem_nhds hx] with y hy1 hy2
    rw [hfg y hy2, hy1]

/-- The affine structure groupoid of `E`: partial homeomorphisms which, together with their
inverses, are locally affine. A charted space with `HasGroupoid M (affineGroupoid E)` is an
affine manifold. -/
def affineGroupoid (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    StructureGroupoid E :=
  (affinePregroupoid (E := E) ⊤).groupoid

/-- The unimodular affine structure groupoid: locally affine with linear part of determinant
`1`. -/
def unimodularAffineGroupoid (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : StructureGroupoid E :=
  (affinePregroupoid (E := E) (MonoidHom.mker LinearMap.det)).groupoid

end Affine

/-- The rational Euler characteristic `Σ_{i=0}^{n} (-1)^i dim_ℚ H_i(M; ℚ)` of a space `M`,
using Mathlib's singular homology with coefficients in `ModuleCat ℚ`, truncated at degree `n`.
For a closed `n`-manifold this is the Euler characteristic, since `H_i(M;ℚ) = 0` for `i > n` and
every `H_i(M;ℚ)` is finite-dimensional (known theorems, not formalized here). -/
def eulerCharUpTo (M : Type) [TopologicalSpace M] (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
    (Module.finrank ℚ
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) i).obj
        (ModuleCat.of ℚ ℚ)).obj (TopCat.of M)) : ℤ)

/-! ## Rank 426: Chern conjecture -/

/-- **Open problem (ProofAtlas rank 426): Chern conjecture on the Euler characteristic of
closed affine manifolds.** (ProofAtlas status: open, with a disputed claimed proof.)

ProofAtlas exact target: "Prove that every closed affine manifold, equivalently every compact
boundaryless manifold whose tangent bundle admits a flat torsion-free connection, has Euler
characteristic zero."

Modelling:
* a closed affine `n`-manifold is a compact Hausdorff space `M` (in `Type`) with an atlas modelled
  on `ℝⁿ = EuclideanSpace ℝ (Fin n)` whose transition maps lie in `affineGroupoid`, i.e. are
  locally affine. This is the first formulation of the target; that it is equivalent to a flat
  torsion-free connection on `TM` is a known theorem not formalized here (Mathlib has covariant
  derivatives and torsion but no curvature tensor);
* the Euler characteristic is `eulerCharUpTo M n` (rational singular homology up to degree `n`,
  see its docstring);
* the dimension is positive, `0 < n`: the conjecture concerns positive-dimensional manifolds, and
  in dimension `0` a point is a closed affine manifold with Euler characteristic `1`. -/
def ChernAffineEuler : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [HasGroupoid M (affineGroupoid (EuclideanSpace ℝ (Fin n)))],
    eulerCharUpTo M n = 0

/-! ## Rank 492: Markus conjecture -/

/-- A curve `γ : ℝ → M` in a manifold with an affine atlas is an affine geodesic if it is
continuous and, read in the chart at `γ t`, it is affine (`s ↦ a + s • w`) for `s` near `t`.
Because transition maps are locally affine, this does not depend on the chart; these are the
geodesics of the flat torsion-free connection whose Christoffel symbols vanish in affine charts. -/
def IsAffineGeodesic {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (γ : ℝ → M) : Prop :=
  Continuous γ ∧ ∀ t : ℝ, ∃ a w : EuclideanSpace ℝ (Fin n),
    ∀ᶠ s in 𝓝 t, chartAt (EuclideanSpace ℝ (Fin n)) (γ t) (γ s) = a + s • w

/-- Geodesic completeness of an affine manifold: for every point `x` and every tangent vector
`v` (in the coordinates of the chart at `x`) there is an affine geodesic defined on all of `ℝ`
through `x` at time `0` with velocity `v`. -/
def IsGeodesicallyComplete (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  ∀ (x : M) (v : EuclideanSpace ℝ (Fin n)), ∃ γ : ℝ → M, IsAffineGeodesic (n := n) γ ∧ γ 0 = x ∧
    HasDerivAt (fun s => chartAt (EuclideanSpace ℝ (Fin n)) x (γ s)) v 0

/-- **Open problem (ProofAtlas rank 492): Markus conjecture.**

ProofAtlas exact target: "Determine whether every compact connected smooth manifold without
boundary carrying a flat torsion-free affine connection and a nowhere-vanishing parallel volume
form is geodesically complete for that affine connection."

The `Prop` below is the affirmative answer; the problem is open.

Modelling:
* a flat torsion-free connection is encoded by an affine atlas (known equivalence, not formalized);
  a nowhere-vanishing parallel volume form then has constant coefficients in affine charts, and
  after composing charts with linear maps it is `dx₁ ∧ … ∧ dxₙ`, so the transition maps have linear
  part of determinant `1`. Hence the hypothesis is modelled as an atlas in
  `unimodularAffineGroupoid` (the converse direction is standard; see the next item);
* the atlas-to-connection direction (an atlas in `unimodularAffineGroupoid` gives a flat
  torsion-free connection with a parallel volume form) is a known equivalence argued here, not
  formalized; a nowhere-vanishing `n`-form orients `M`, which the determinant-`1` atlas encodes;
* `M` is a compact, connected Hausdorff space in `Type`, modelled on `ℝⁿ` without boundary;
* geodesic completeness is `IsGeodesicallyComplete`: every affine geodesic germ extends to `ℝ`. -/
def MarkusConjecture : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [HasGroupoid M (unimodularAffineGroupoid (EuclideanSpace ℝ (Fin n)))],
    IsGeodesicallyComplete n M

/-! ## Rank 444: Moore's conjecture -/

/-- `g` has finite order a power of `p`. -/
def IsPPrimary {G : Type*} [Monoid G] (p : ℕ) (g : G) : Prop := ∃ k : ℕ, g ^ (p ^ k) = 1

/-- `X` has a homotopy exponent at `p`: one power `p^e` kills the `p`-primary torsion of every
`π_i(X, x)`, `i ≥ 2`. (`π_1` is trivial for the simply connected `X` considered below.) -/
def HasHomotopyExponent (X : Type) [TopologicalSpace X] (x : X) (p : ℕ) : Prop :=
  ∃ e : ℕ, ∀ i : ℕ, ∀ g : π_ (i + 2) X x, IsPPrimary p g → g ^ (p ^ e) = 1

/-- `⊕_{i ≥ 2} π_i(X, x) ⊗ ℚ` is a finite-dimensional `ℚ`-vector space. -/
def IsRationallyElliptic (X : Type) [TopologicalSpace X] (x : X) : Prop :=
  Module.Finite ℚ (DirectSum ℕ fun i => TensorProduct ℤ ℚ (Additive (π_ (i + 2) X x)))

/-- **Open problem (ProofAtlas rank 444): Moore's conjecture on homotopy exponents.**

ProofAtlas exact target: "For every simply connected finite CW-complex X, the following are
equivalent: (a) ⊕_{i≥2}π_i(X)⊗Q is finite-dimensional; (b) for some prime p a power p^e
annihilates all p-primary torsion in all π_i(X); (c) for every prime p there exists such a power
p^{e(p)}."

Modelling:
* a simply connected finite CW complex is a Hausdorff space `X` (in `Type`) with a classical CW
  structure on `Set.univ` (`Topology.CWComplex`) having finitely many cells
  (`Topology.RelCWComplex.Finite`) and `SimplyConnectedSpace X`; the base point `x` is arbitrary
  (simply connected spaces are path connected);
* `π_i(X) ⊗ ℚ` is `ℚ ⊗[ℤ] π_i(X, x)` for the abelian group `π_i(X, x)`, `i ≥ 2`, and (a) is
  `IsRationallyElliptic`;
* "p-primary torsion in all π_i(X)" ranges over `i ≥ 2` (`π_1` is trivial); (b) is
  `∃ p prime, HasHomotopyExponent X x p` and (c) is `∀ p prime, HasHomotopyExponent X x p`;
* "the following are equivalent" is `(a ↔ b) ∧ (a ↔ c)`. -/
def MooreConjecture : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    [Topology.RelCWComplex.Finite (Set.univ : Set X)] [SimplyConnectedSpace X] (x : X),
    (IsRationallyElliptic X x ↔ ∃ p : ℕ, p.Prime ∧ HasHomotopyExponent X x p) ∧
    (IsRationallyElliptic X x ↔ ∀ p : ℕ, p.Prime → HasHomotopyExponent X x p)

/-! ## Known algebraic results around the 11/8-conjecture (rank 213): the `E₈` form -/

open Matrix

/-- The Gram matrix of the `E₈` root lattice in the basis of simple roots, read off Mathlib's
Coxeter matrix `CoxeterMatrix.E₈`: `2` on the diagonal, `-1` where `m_{ij} = 3` (an edge of the
Dynkin diagram), `0` otherwise. -/
def e8Gram : Matrix (Fin 8) (Fin 8) ℤ :=
  Matrix.of fun i j => if i = j then 2 else if CoxeterMatrix.E₈ i j = 3 then -1 else 0

/-- The integer inverse of `e8Gram` (used to prove unimodularity). -/
def e8GramInv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
     10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
     4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2]

/-- Finite check: the explicit entries of `e8Gram`. -/
theorem e8Gram_explicit : e8Gram =
    !![2, 0, -1, 0, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0, 0, 0; -1, 0, 2, -1, 0, 0, 0, 0;
       0, -1, -1, 2, -1, 0, 0, 0; 0, 0, 0, -1, 2, -1, 0, 0; 0, 0, 0, 0, -1, 2, -1, 0;
       0, 0, 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, 0, 0, -1, 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Known result (finite check): the `E₈` Gram matrix is symmetric. -/
theorem e8Gram_transpose : e8Gramᵀ = e8Gram := by
  rw [e8Gram_explicit]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Finite check: `e8GramInv` is a right inverse of `e8Gram` over `ℤ`. -/
theorem e8Gram_mul_inv : e8Gram * e8GramInv = 1 := by
  rw [e8Gram_explicit]; ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- Known result: the `E₈` form is even, `xᵀ G x ∈ 2ℤ` for every `x ∈ ℤ⁸` (in particular all
diagonal entries are even). Reference: J.-P. Serre, *A Course in Arithmetic*, Ch. V, §1.4. -/
theorem e8Gram_even (x : Fin 8 → ℤ) : Even (x ⬝ᵥ (e8Gram *ᵥ x)) := by
  rw [e8Gram_explicit]
  refine ⟨x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 + x 5 ^ 2 + x 6 ^ 2 + x 7 ^ 2
    - x 0 * x 2 - x 1 * x 3 - x 2 * x 3 - x 3 * x 4 - x 4 * x 5 - x 5 * x 6 - x 6 * x 7, ?_⟩
  simp [dotProduct, mulVec, Fin.sum_univ_succ]
  ring

/-- Known result: the `E₈` form is positive definite (over `ℚ`, via its `LDLᵀ` decomposition
with pivots `2, 2, 3/2, 5/6, 4/5, 3/4, 2/3, 1/2`). Reference: Serre, *A Course in Arithmetic*,
Ch. V, §1.4. -/
theorem e8Gram_posDef : (e8Gram.map (Int.cast : ℤ → ℚ)).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [e8Gram_explicit]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    rw [e8Gram_explicit]
    have key : star x ⬝ᵥ ((Matrix.map !![2, 0, -1, 0, 0, 0, 0, 0; 0, 2, 0, -1, 0, 0, 0, 0;
        -1, 0, 2, -1, 0, 0, 0, 0; 0, -1, -1, 2, -1, 0, 0, 0; 0, 0, 0, -1, 2, -1, 0, 0;
        0, 0, 0, 0, -1, 2, -1, 0; 0, 0, 0, 0, 0, -1, 2, -1; 0, 0, 0, 0, 0, 0, -1, 2]
        (Int.cast : ℤ → ℚ)) *ᵥ x) =
      2 * (x 0 - x 2 / 2) ^ 2 + 2 * (x 1 - x 3 / 2) ^ 2 + 3 / 2 * (x 2 - 2 / 3 * x 3) ^ 2
      + 5 / 6 * (x 3 - 6 / 5 * x 4) ^ 2 + 4 / 5 * (x 4 - 5 / 4 * x 5) ^ 2
      + 3 / 4 * (x 5 - 4 / 3 * x 6) ^ 2 + 2 / 3 * (x 6 - 3 / 2 * x 7) ^ 2 + 1 / 2 * x 7 ^ 2 := by
      simp [dotProduct, mulVec, Fin.sum_univ_succ]
      ring
    rw [key]
    by_contra hle
    push Not at hle
    have h0 := sq_nonneg (x 0 - x 2 / 2)
    have h1 := sq_nonneg (x 1 - x 3 / 2)
    have h2 := sq_nonneg (x 2 - 2 / 3 * x 3)
    have h3 := sq_nonneg (x 3 - 6 / 5 * x 4)
    have h4 := sq_nonneg (x 4 - 5 / 4 * x 5)
    have h5 := sq_nonneg (x 5 - 4 / 3 * x 6)
    have h6 := sq_nonneg (x 6 - 3 / 2 * x 7)
    have h7 := sq_nonneg (x 7)
    have s7 : x 7 ^ 2 = 0 := by linarith
    have s6 : (x 6 - 3 / 2 * x 7) ^ 2 = 0 := by linarith
    have s5 : (x 5 - 4 / 3 * x 6) ^ 2 = 0 := by linarith
    have s4 : (x 4 - 5 / 4 * x 5) ^ 2 = 0 := by linarith
    have s3 : (x 3 - 6 / 5 * x 4) ^ 2 = 0 := by linarith
    have s2 : (x 2 - 2 / 3 * x 3) ^ 2 = 0 := by linarith
    have s1 : (x 1 - x 3 / 2) ^ 2 = 0 := by linarith
    have s0 : (x 0 - x 2 / 2) ^ 2 = 0 := by linarith
    have e7 : x 7 = 0 := pow_eq_zero_iff two_ne_zero |>.mp s7
    have e6 : x 6 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s6; rw [e7] at this; linarith
    have e5 : x 5 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s5; rw [e6] at this; linarith
    have e4 : x 4 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s4; rw [e5] at this; linarith
    have e3 : x 3 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s3; rw [e4] at this; linarith
    have e2 : x 2 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s2; rw [e3] at this; linarith
    have e1 : x 1 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s1; rw [e3] at this; linarith
    have e0 : x 0 = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.mp s0; rw [e2] at this; linarith
    apply hx
    funext i; fin_cases i <;> simp [e0, e1, e2, e3, e4, e5, e6, e7]

/-- Known result: the `E₈` form is unimodular, `det = 1`. (From `e8Gram_mul_inv` the
determinant is a unit of `ℤ`, and it is positive by positive definiteness.) Reference: Serre,
*A Course in Arithmetic*, Ch. V, §1.4. -/
theorem e8Gram_det : e8Gram.det = 1 := by
  have hu : e8Gram.det * e8GramInv.det = 1 := by rw [← det_mul, e8Gram_mul_inv, det_one]
  have hpos : (0 : ℚ) < (e8Gram.det : ℚ) := by
    have := e8Gram_posDef.det_pos
    have hm : ((e8Gram.det : ℤ) : ℚ) = (e8Gram.map (Int.cast : ℤ → ℚ)).det :=
      RingHom.map_det (Int.castRingHom ℚ) e8Gram
    rw [hm]; exact this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
  · exact h
  · rw [h] at hpos; norm_num at hpos

/-- Known result (summary): the `E₈` form is an even, unimodular, positive definite symmetric
integral form of rank `8`. Reference: Serre, *A Course in Arithmetic*, Ch. V, §1.4. -/
theorem e8_even_unimodular_posDef :
    e8Gramᵀ = e8Gram ∧ (∀ x : Fin 8 → ℤ, Even (x ⬝ᵥ (e8Gram *ᵥ x))) ∧ e8Gram.det = 1 ∧
      (e8Gram.map (Int.cast : ℤ → ℚ)).PosDef :=
  ⟨e8Gram_transpose, e8Gram_even, e8Gram_det, e8Gram_posDef⟩

end CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology

end

#print axioms CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology.e8Gram_transpose
#print axioms CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology.e8Gram_even
#print axioms CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology.e8Gram_posDef
#print axioms CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology.e8Gram_det
#print axioms CryptoLean.OpenProblems.GeometryTopology.FourManifoldsTopology.e8_even_unimodular_posDef
