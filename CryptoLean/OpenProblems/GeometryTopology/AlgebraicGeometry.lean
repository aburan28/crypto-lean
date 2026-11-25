import Mathlib

/-!
# Algebraic geometry open problems (ProofAtlas geometry & topology list)

None of the problems below is solved here, and nothing in this file suggests that any of them
is resolved. One problem (Hartshorne's codimension-two conjecture, rank 276) can be stated
faithfully with Mathlib's commutative algebra, through the classical dictionary between closed
subvarieties of `ℙᴺ_ℂ` and homogeneous prime ideals of `ℂ[x₀,…,x_N]`; it is the unproved
`def … : Prop` `HartshorneCodimTwoConjecture`. All the others need objects that Mathlib does
not have yet, and are recorded in the second table.

## Mathlib spot-check (Mathlib pinned in this repository)

What exists: schemes, `Proj` of a graded ring (`Mathlib/AlgebraicGeometry/ProjectiveSpectrum`),
smooth / proper / étale morphisms of schemes, sheaves of modules on a scheme
(`AlgebraicGeometry.Scheme.Modules`) and `tilde`, algebraic cycles as locally finite functions
(`AlgebraicGeometry.AlgebraicCycle`, with push-forward and Weil divisors, but no rational
equivalence, Chow groups, intersection product or cycle class map), order of vanishing,
pro-étale `ℓ`-adic cohomology `Hⁱ(X, ℤ_ℓ)` of a scheme
(`AlgebraicGeometry.Scheme.EllAdicCohomology`, without Galois action, Tate twists or comparison
with étale cohomology), derived categories of abelian categories with their pretriangulated
structure, smooth manifolds over `ℂ` as charted spaces, regular local rings
(`IsRegularLocalRing`), Krull dimension, and homogeneous polynomials.

Searched for and absent (`grep` over `.lake/packages/mathlib/Mathlib`): ample / very ample /
nef line bundles or divisors, the canonical sheaf `K_X` and the sheaf of differentials of a
scheme, coherent sheaves and `D^b_coh(X)`, Kähler manifolds, singular / de Rham / Hodge
cohomology of varieties and Hodge structures, Gauss–Manin connection, analytification `X(ℂ)^an`
and its fundamental group, flips / klt / log canonical pairs / discrepancies, Gromov–Witten
invariants and quantum cohomology, exceptional collections, Hilbert schemes and normal bundles,
holomorphic jet differentials and entire curves.

## Open problems stated as `Prop`s

| rank | problem | declaration |
|------|---------|-------------|
| 276 | Hartshorne conjecture on complete intersections in codimension two | `HartshorneCodimTwoConjecture` |

## Open problems not expressible faithfully with Mathlib today

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 4 | Hodge conjecture | singular cohomology `H^{2p}(X(ℂ)^an, ℚ)` of the analytification of a smooth complex projective variety, its Hodge decomposition (Dolbeault/Hodge theory on compact Kähler manifolds) and hence rational Hodge classes, rational equivalence/Chow groups of cycles and the cycle class map `CH^p(X)_ℚ → H^{2p}(X, ℚ)` |
| 15 | Tate conjecture for algebraic cycles | étale cohomology `H^{2i}(X_{k̄}, ℚ_ℓ(i))` with Tate twist and its continuous `Gal(k̄/k)`-action (Mathlib only has untwisted pro-étale `Hⁱ(X, ℤ_ℓ)` without Galois action or comparison theorem), Chow groups of codimension-`i` cycles, the `ℓ`-adic cycle class map |
| 67 | Termination of flips (MMP) | canonical divisor `K_X`, `ℚ`-Cartier `ℚ`-divisors and their pull-back, discrepancies, klt / log canonical pairs, relative ampleness and Picard number one contractions, flips |
| 92 | Green–Griffiths–Lang conjecture | varieties of general type (canonical sheaf, Kodaira dimension / Iitaka dimension, resolution of singularities), complex analytic space `X(ℂ)^an` of a projective variety, entire holomorphic curves `ℂ → X(ℂ)^an` and their Zariski closure, jet differentials |
| 139 | Grothendieck's variational Hodge conjecture | relative algebraic de Rham cohomology `R^{2p}f_*Ω^•_{X/S}` as a vector bundle, the Gauss–Manin connection and horizontal sections, the de Rham cycle class of an algebraic cycle on a fiber |
| 191 | Virasoro conjecture for Gromov–Witten invariants | moduli stacks of stable maps and virtual fundamental classes, descendant Gromov–Witten invariants and the total descendant potential over the Novikov ring, cohomology of `X` with Hodge grading (needed for the Eguchi–Hori–Xiong–Katz operators `L_k^X`) |
| 208 | Kawamata K-equivalence ⇒ D-equivalence | coherent sheaves on a scheme and the bounded derived category `D^b_coh(X)` as a triangulated category (Mathlib has `DerivedCategory C` only for an abelian `C`, no coherent subcategory), canonical divisor `K_X` with pull-back and linear equivalence |
| 209 | Morrison–Kawamata cone conjecture | klt pairs and numerical triviality of `K_X + Δ`, Néron–Severi space `N¹(X)_ℝ`, effective nef and effective movable cones, `Aut(X, Δ)` and pseudo-automorphisms `PsAut(X, Δ)` acting on them, rational polyhedral fundamental domains for such actions |
| 254 | Dubrovin conjecture for Fano manifolds | (big) quantum cohomology and its semisimplicity (Gromov–Witten invariants), the quantum differential equation with its Stokes and central connection matrices, `D^b_coh(F)` and full exceptional collections, Euler pairing `χ(E_i, E_j)` and Chern character / Gamma-modified `Ch(E)`, Fano manifolds (anti-canonical ampleness) |
| 349 | Clemens conjecture on the general quintic threefold | "general" member of the linear system of quintics as a Zariski-dense open condition on the parameter space `ℙ¹²⁵`, smooth rational curves of degree `d` in a hypersurface as points of a Hilbert scheme, normal bundles `N_{C/X}` and their splitting / rigidity (`h⁰(N_{C/X}) = 0`) |
| 356 | Finiteness of deformation types of compact hyperkähler manifolds | compact Kähler manifolds, holomorphic `2`-forms `H⁰(X, Ω²_X)` and their nondegeneracy, simple connectivity of a complex manifold paired with the Kähler condition, smooth proper holomorphic families over connected complex bases and the deformation equivalence they generate |
| 392 | Fujita very ampleness conjecture | ample divisors / line bundles, very ampleness (closed embedding defined by the complete linear system), the canonical divisor `K_X` of a smooth projective variety, integral multiples and sums of divisors classes |
| 397 | Campana–Peternell conjecture | tangent bundle of a smooth projective variety as a vector bundle, nefness of vector bundles (via `𝒪_{ℙ(T_X)}(1)`), Fano varieties (ample `-K_X`), rational homogeneous varieties `G/P` for semisimple algebraic groups `G` and parabolic subgroups `P` |
| 436 | Rational curves on simply connected Calabi–Yau threefolds | canonical sheaf `K_X` and its triviality `K_X ≅ 𝒪_X`, coherent cohomology `h¹(X, 𝒪_X)` of a scheme (Mathlib's site cohomology is not connected to `𝒪_X` of a scheme), fundamental group of the analytification `X(ℂ)^an`, the projective line `ℙ¹_ℂ` as a named scheme with non-constant morphisms to `X` (expressible via `Proj`, but useless without the hypotheses) |

No known theorem is proved in this module: none of the classical special cases (Lefschetz
`(1,1)`, Tate for divisors on abelian varieties over finite fields, termination of flips in
dimension `3`, Fujita for curves, …) is expressible without the objects listed above, and
filler theorems are deliberately omitted.
-/

namespace CryptoLean.OpenProblems.GeometryTopology.AlgebraicGeometry

open MvPolynomial

/-- The homogeneous coordinate ring `ℂ[x₀, …, x_N]` of complex projective space `ℙᴺ`. -/
abbrev CoordRing (N : ℕ) : Type := MvPolynomial (Fin (N + 1)) ℂ

/-- An ideal of `ℂ[x₀,…,x_N]` is homogeneous iff it contains every homogeneous component of
each of its elements (equivalently, it is generated by homogeneous polynomials). -/
def IsHomogeneousIdeal {N : ℕ} (I : Ideal (CoordRing N)) : Prop :=
  ∀ p ∈ I, ∀ n : ℕ, homogeneousComponent n p ∈ I

/-- The irrelevant ideal `S₊ = (x₀, …, x_N)` of `ℂ[x₀,…,x_N]`. -/
noncomputable def irrelevant (N : ℕ) : Ideal (CoordRing N) :=
  Ideal.span (Set.range (fun i : Fin (N + 1) => (X i : CoordRing N)))

/-- The projective variety `V(I) ⊆ ℙᴺ_ℂ` of a homogeneous prime ideal `I` is *smooth* over `ℂ`:
every local ring of the punctured affine cone `Spec(S/I) ∖ V(S₊)` is regular, i.e. for every
prime `Q` of `S/I` not containing the image of the irrelevant ideal, `(S/I)_Q` is a regular
local ring. (Over the perfect field `ℂ`, smooth ⇔ regular for schemes of finite type, and the
punctured cone is a `𝔾ₘ`-torsor over `V(I)`, so regularity of the cone away from the vertex is
equivalent to regularity of `V(I)`.) -/
def IsSmoothProjVariety {N : ℕ} (I : Ideal (CoordRing N)) : Prop :=
  ∀ Q : PrimeSpectrum (CoordRing N ⧸ I),
    ¬ (irrelevant N).map (Ideal.Quotient.mk I) ≤ Q.asIdeal →
      IsRegularLocalRing (Localization.AtPrime Q.asIdeal)

/-- `V(I) ⊆ ℙᴺ` is, scheme-theoretically, the intersection of the two hypersurfaces `V(f)`,
`V(g)`: the saturation `((f, g) : S₊^∞)` of the ideal `(f, g)` with respect to the irrelevant
ideal equals `I` (closed subschemes of `ℙᴺ` correspond to saturated homogeneous ideals). -/
def IsSchemeTheoreticIntersection {N : ℕ} (I : Ideal (CoordRing N)) (f g : CoordRing N) :
    Prop :=
  ∀ h : CoordRing N, h ∈ I ↔ ∃ k : ℕ, ∀ i : Fin (N + 1), X i ^ k * h ∈ Ideal.span {f, g}

/-- **Hartshorne's conjecture on complete intersections in codimension two** (ProofAtlas
rank 276). OPEN; not proved here.

ProofAtlas exactTarget: "Prove that for every integer N >= 7, every smooth codimension-two
subvariety X of complex projective space P^N is the scheme-theoretic intersection of two
hypersurfaces."

Modelling (classical dictionary, no change of content):
* a closed subvariety `X ⊆ ℙᴺ_ℂ` (integral closed subscheme) is given by its homogeneous
  ideal `I`, a homogeneous prime of `S = ℂ[x₀,…,x_N]` not containing `S₊`; such `I` is
  saturated, so `X ↦ I` is a bijection onto these primes. Subvarieties are taken irreducible;
  for `N ≥ 7` a smooth codimension-two subvariety has dimension `≥ 5` and is connected
  (Barth–Larsen / Fulton–Hansen), hence irreducible, so no case is lost;
* codimension two is `dim S/I = (N - 2) + 1 = N - 1` (Krull dimension of the affine cone); this
  also forces `S₊ ⊄ I`, i.e. `X ≠ ∅`;
* smoothness of `X` over `ℂ` is `IsSmoothProjVariety I` (regularity of the punctured cone);
* a hypersurface is `V(f)` for a nonzero homogeneous `f` of positive degree, and
  "scheme-theoretic intersection of two hypersurfaces" is `IsSchemeTheoreticIntersection`:
  the saturation of `(f, g)` equals `I`. -/
def HartshorneCodimTwoConjecture : Prop :=
  ∀ N : ℕ, 7 ≤ N →
    ∀ I : Ideal (CoordRing N), I.IsPrime → IsHomogeneousIdeal I →
      ringKrullDim (CoordRing N ⧸ I) = ((N - 1 : ℕ) : WithBot ℕ∞) →
      IsSmoothProjVariety I →
        ∃ (f g : CoordRing N) (d e : ℕ), 0 < d ∧ 0 < e ∧ f ≠ 0 ∧ g ≠ 0 ∧
          f.IsHomogeneous d ∧ g.IsHomogeneous e ∧ IsSchemeTheoreticIntersection I f g

end CryptoLean.OpenProblems.GeometryTopology.AlgebraicGeometry
