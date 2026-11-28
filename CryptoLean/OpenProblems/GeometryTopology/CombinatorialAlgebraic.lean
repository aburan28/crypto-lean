import Mathlib

/-!
# Combinatorial and algebraic open problems in geometry and topology (ProofAtlas list)

**None of the problems below is solved here.** Each open problem is either an unproved
`def … : Prop` whose docstring quotes the ProofAtlas `exactTarget` and lists every modelling
choice, or a row of the table of problems that cannot be stated faithfully with Mathlib today.

## Open problems stated as `Prop`s

| rank | problem | declaration |
|------|---------|-------------|
| 348 | Whitehead asphericity conjecture | `WhiteheadAsphericity` |
| 399 | Auslander conjecture | `AuslanderConjecture` |
| 408 | Residual finiteness of all Artin–Tits groups | `ArtinTitsResiduallyFinite` |
| 425 | Segre–Harbourne–Gimigliano–Hirschowitz conjecture (Cremona-reduced form) | `SHGHConjecture` |
| 479 | Word problem for all Artin–Tits groups | `ArtinTitsWordProblem` |
| 496 | Charney–Davis conjecture | `CharneyDavisConjecture` |

## Open problems not expressible faithfully with Mathlib today

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 393 | F-conjecture for the nef cone of `M̄_{0,n}` | the moduli space `M̄_{0,n}` of stable `n`-pointed genus-0 curves (as a smooth projective variety / scheme), its divisor class group `N¹`, curve classes and the intersection pairing of divisors with curves, the nef cone and closed Mori cone, the one-dimensional boundary strata (F-curves) |
| 410 | Freyd's generating hypothesis | spectra and the stable homotopy category (finite spectra, homotopy classes of maps `[X,Y]`), stable homotopy groups `π_*X` as graded modules over the stable stems `π_*S` |

## Known results proved here

* `artin_of_not_isOfFinOrder`: every standard generator of every Artin–Tits group has infinite
  order (the length homomorphism to `ℤ`).
* `artinAllTwo_comm`: the Artin–Tits group of the Coxeter matrix with all off-diagonal labels
  `2` is commutative (it is free abelian; only commutativity is proved here).
* `auslander_dim_one`: the Auslander conjecture holds in dimension `1`; indeed every subgroup of
  `Aff(ℝ¹)` is solvable.
-/

open scoped BigOperators

namespace CryptoLean.OpenProblems.GeometryTopology.CombinatorialAlgebraic

/-! ## Artin–Tits groups (ranks 408, 479) -/

section Artin

variable {B : Type*}

/-- The Artin (braid) relator attached to `i, i'` and a Coxeter matrix `M`:
`Π(i,i';m) · Π(i',i;m)⁻¹` where `Π(a,b;m)` is the alternating word of length `m = M i i'`
(Mathlib's `CoxeterSystem.alternatingWord`). For `m = 0` (Mathlib's encoding of the label `∞`)
both words are empty and the relator is trivial, as it should be; for `i = i'` it is trivial. -/
def artinRelator (M : CoxeterMatrix B) (i i' : B) : FreeGroup B :=
  ((CoxeterSystem.alternatingWord i i' (M i i')).map FreeGroup.of).prod *
    ((CoxeterSystem.alternatingWord i' i (M i i')).map FreeGroup.of).prod⁻¹

/-- The set of Artin relators of `M`. -/
def artinRelators (M : CoxeterMatrix B) : Set (FreeGroup B) :=
  Set.range fun p : B × B => artinRelator M p.1 p.2

/-- The Artin–Tits group of a Coxeter matrix `M`, as a `PresentedGroup`:
generators `s_i` and, for every pair with `m_{ii'} < ∞`, the braid relation
`s_i s_{i'} s_i ⋯ = s_{i'} s_i s_{i'} ⋯` (`m_{ii'}` letters on each side). -/
abbrev ArtinGroup (M : CoxeterMatrix B) := PresentedGroup (artinRelators M)

/-- **Rank 479 (open).** ProofAtlas exactTarget: "Decide whether every Artin-Tits group
associated with a finite Coxeter matrix has a decidable word problem: for each such fixed group
there is an algorithm which, given a finite word in its standard generators and their inverses,
decides whether the word is the identity. No Coxeter-type restriction is imposed. A uniform
algorithm from the matrix and word would suffice, but uniformity is not imposed beyond the
classical every-group formulation."

Modelling: a finite Coxeter matrix is a Mathlib `CoxeterMatrix (Fin n)` (label `∞` encoded as
`0`); the group is `ArtinGroup M`; a word in the generators and their inverses is a
`List (Fin n × Bool)` (Mathlib's `FreeGroup` letter convention, `true` = the generator); an
algorithm is a computable predicate in Mathlib's `ComputablePred` sense (partial recursive
functions over the standard `Primcodable` encoding). The `Prop` is the positive answer
("every such group has decidable word problem"); a negative answer is its negation. -/
def ArtinTitsWordProblem : Prop :=
  ∀ (n : ℕ) (M : CoxeterMatrix (Fin n)),
    ComputablePred fun w : List (Fin n × Bool) =>
      (PresentedGroup.mk (artinRelators M) (FreeGroup.mk w) : ArtinGroup M) = 1

/-- **Rank 408 (open).** ProofAtlas exactTarget: "Decide whether every Artin-Tits group
associated with a finite Coxeter matrix is residually finite: for each nonidentity element g,
there exists a homomorphism to a finite group whose value on g is nonidentity. No spherical,
FC, triangle, or other diagram restriction is imposed."

Modelling: as in `ArtinTitsWordProblem`; finite groups are taken in `Type` (no loss: a finite
group is isomorphic to one in `Type`). The `Prop` is the positive answer. -/
def ArtinTitsResiduallyFinite : Prop :=
  ∀ (n : ℕ) (M : CoxeterMatrix (Fin n)) (g : ArtinGroup M), g ≠ 1 →
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : ArtinGroup M →* H), φ g ≠ 1

/-- **Known result** (classical; e.g. Paris, *Artin groups and Artin monoids*, or any survey of
Artin–Tits groups: the "length" homomorphism `A_M → ℤ`, `s_i ↦ 1`). Every standard generator
of every Artin–Tits group has infinite order. -/
theorem artin_of_not_isOfFinOrder (M : CoxeterMatrix B) (i : B) :
    ¬ IsOfFinOrder (PresentedGroup.of i : ArtinGroup M) := by
  have hrel : ∀ r ∈ artinRelators M,
      FreeGroup.lift (fun _ : B => Multiplicative.ofAdd (1 : ℤ)) r = 1 := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    simp only [artinRelator, map_mul, map_inv, map_list_prod, List.map_map]
    have h : ∀ l : List B, (l.map (⇑(FreeGroup.lift fun _ : B => Multiplicative.ofAdd (1 : ℤ)) ∘
        FreeGroup.of)).prod = Multiplicative.ofAdd (1 : ℤ) ^ l.length := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih => simp [ih, pow_succ, mul_comm]
    rw [h, h, CoxeterSystem.length_alternatingWord, CoxeterSystem.length_alternatingWord,
      mul_inv_cancel]
  intro hfin
  obtain ⟨k, hk, hk0⟩ := hfin.exists_pow_eq_one
  have hk' : Multiplicative.ofAdd (1 : ℤ) ^ k = 1 := by
    have := congrArg (PresentedGroup.toGroup hrel) hk0
    rw [map_pow, PresentedGroup.toGroup.of] at this
    simpa using this
  have : ((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd = (1 : Multiplicative ℤ).toAdd := by
    rw [hk']
  simp at this
  omega

/-- The Coxeter matrix on `Fin n` with all off-diagonal labels `2`. -/
def allTwo (n : ℕ) : CoxeterMatrix (Fin n) where
  M := Matrix.of fun i j => if i = j then 1 else 2
  isSymm := by
    ext i j
    simp [Matrix.transpose_apply, eq_comm]
  diagonal i := by simp
  off_diagonal i j h := by simp [h]

/-- **Known result** (classical: the right-angled Artin group of the complete graph is the free
abelian group `ℤⁿ`). The Artin–Tits group of the all-`2` Coxeter matrix is commutative. -/
theorem artinAllTwo_comm (n : ℕ) (x y : ArtinGroup (allTwo n)) : x * y = y * x := by
  have gen : ∀ i j : Fin n,
      (PresentedGroup.of i : ArtinGroup (allTwo n)) * PresentedGroup.of j =
        PresentedGroup.of j * PresentedGroup.of i := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    have hm : (allTwo n) i j = 2 := by simp [allTwo, hij]
    have hmem : artinRelator (allTwo n) i j ∈ artinRelators (allTwo n) := ⟨(i, j), rfl⟩
    have h1 := PresentedGroup.one_of_mem hmem
    rw [artinRelator, hm] at h1
    simp only [CoxeterSystem.alternatingWord, List.concat_eq_append, List.nil_append,
      List.cons_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      mul_inv_rev] at h1
    have := eq_of_mul_inv_eq_one (a := (PresentedGroup.mk _ (FreeGroup.of i * FreeGroup.of j) :
      ArtinGroup (allTwo n))) (b := PresentedGroup.mk _ (FreeGroup.of j * FreeGroup.of i))
      (by simpa [mul_assoc] using h1)
    exact this
  have hcent : ∀ i : Fin n, ∀ z : ArtinGroup (allTwo n),
      PresentedGroup.of i * z = z * PresentedGroup.of i := by
    intro i z
    have := PresentedGroup.generated_by (artinRelators (allTwo n))
      (Subgroup.centralizer {PresentedGroup.of i})
      (fun j => Subgroup.mem_centralizer_singleton_iff.mpr (gen j i)) z
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have := PresentedGroup.generated_by (artinRelators (allTwo n)) (Subgroup.centralizer {y})
    (fun j => Subgroup.mem_centralizer_singleton_iff.mpr (hcent j y)) x
  exact Subgroup.mem_centralizer_singleton_iff.mp this

end Artin

/-! ## Auslander conjecture (rank 399) -/

section Auslander

/-- The affine group `Aff(ℝⁿ)` (Mathlib's group of affine automorphisms of `ℝⁿ = Fin n → ℝ`). -/
abbrev Aff (n : ℕ) := (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ)

/-- `Γ ≤ Aff(ℝⁿ)` is an *affine crystallographic group*: it acts properly discontinuously on
`ℝⁿ` (for all compact `K, L`, only finitely many `γ ∈ Γ` have `γ K ∩ L ≠ ∅`; this is Mathlib's
`ProperlyDiscontinuousSMul` condition written out, since Mathlib has no action instance of the
affine group) and cocompactly (some compact `K` has `Γ·K = ℝⁿ`). -/
def IsAffineCrystallographic {n : ℕ} (Γ : Subgroup (Aff n)) : Prop :=
  (∀ K L : Set (Fin n → ℝ), IsCompact K → IsCompact L →
      {γ : Aff n | γ ∈ Γ ∧ ((γ '' K) ∩ L).Nonempty}.Finite) ∧
    ∃ K : Set (Fin n → ℝ), IsCompact K ∧ ∀ x, ∃ γ ∈ Γ, x ∈ γ '' K

/-- **Rank 399 (open).** ProofAtlas exactTarget: "Prove or disprove that every affine
crystallographic group is virtually solvable, equivalently that the fundamental group of every
compact complete affine manifold is virtually polycyclic."

Modelling: the first formulation; affine crystallographic groups as in
`IsAffineCrystallographic`; "virtually solvable" = has a finite-index subgroup that is solvable
(`Subgroup.FiniteIndex`, `IsSolvable`). The `Prop` is the conjectured (positive) answer. -/
def AuslanderConjecture : Prop :=
  ∀ (n : ℕ) (Γ : Subgroup (Aff n)), IsAffineCrystallographic Γ →
    ∃ H : Subgroup Γ, H.FiniteIndex ∧ Group.IsSolvable H

lemma linearEquiv_fin_one_comm (f g : (Fin 1 → ℝ) ≃ₗ[ℝ] (Fin 1 → ℝ)) : f * g = g * f := by
  have key : ∀ (h : (Fin 1 → ℝ) ≃ₗ[ℝ] (Fin 1 → ℝ)) (x : Fin 1 → ℝ),
      h x = (x 0 * h (fun _ => 1) 0) • (fun _ => (1 : ℝ)) := by
    intro h x
    have hx : x = x 0 • (fun _ => (1 : ℝ)) := by
      funext i; fin_cases i; simp
    have h1 : h (fun _ => 1) = (h (fun _ => 1) 0) • (fun _ => (1 : ℝ)) := by
      funext i; fin_cases i; simp
    conv_lhs => rw [hx, map_smul, h1, smul_smul]
  ext x i
  show f (g x) i = g (f x) i
  rw [key f (g x), key g (f x), key g x, key f x]
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-- **Known result** (classical; the affine group of the line is metabelian, see e.g.
Abels, *Properly discontinuous groups of affine transformations: a survey*, Geom. Dedicata 87
(2001)). The Auslander conjecture holds in dimension one: every subgroup of `Aff(ℝ¹)` — in
particular every affine crystallographic one — is solvable, so it is its own finite-index
solvable subgroup. -/
theorem auslander_dim_one (Γ : Subgroup (Aff 1)) (_ : IsAffineCrystallographic Γ) :
    ∃ H : Subgroup Γ, H.FiniteIndex ∧ Group.IsSolvable H := by
  have : Group.IsSolvable ((Fin 1 → ℝ) ≃ₗ[ℝ] (Fin 1 → ℝ)) :=
    Group.isSolvable_of_comm linearEquiv_fin_one_comm
  have : Group.IsSolvable (Aff 1) := by
    refine Group.isSolvable_of_ker_le_range (AffineEquiv.constVAddHom ℝ (Fin 1 → ℝ))
      (AffineEquiv.linearHom) ?_
    intro e he
    refine ⟨Multiplicative.ofAdd (e 0), ?_⟩
    have hl : e.linear = LinearEquiv.refl ℝ _ := he
    ext x i
    have := e.map_vadd 0 x
    simp only [vadd_eq_add, add_zero, hl, LinearEquiv.refl_apply] at this
    simp [AffineEquiv.constVAddHom, AffineEquiv.constVAdd, this, add_comm]
  exact ⟨⊤, inferInstance, inferInstance⟩

end Auslander

/-! ## Whitehead asphericity conjecture (rank 348) -/

section Whitehead

/-- A subset `S` of a space is *aspherical*: path-connected, and `πₙ(S, x)` is trivial for all
`n ≥ 2` and all base points. -/
def IsAspherical {X : Type} [TopologicalSpace X] (S : Set X) : Prop :=
  IsPathConnected S ∧ ∀ n : ℕ, 2 ≤ n → ∀ x : S, Subsingleton (HomotopyGroup.Pi n S x)

/-- **Rank 348 (open; ProofAtlas status: open, disputed claims).** ProofAtlas exactTarget:
"Decide whether every connected subcomplex of an aspherical two-dimensional CW-complex is
aspherical, equivalently whether every subpresentation of an aspherical presentation is
aspherical."

Modelling: the first (CW) formulation. A CW complex is Mathlib's classical `CWComplex C` on a
subset `C` of a Hausdorff space `X : Type`; "two-dimensional" = no cells of dimension `> 2`;
subcomplexes are Mathlib's `RelCWComplex.Subcomplex C`; asphericity is `IsAspherical`
(path-connected with vanishing higher homotopy groups — for CW complexes path-connected and
connected agree, and the hypothesis on the subcomplex is stated as connectedness as in the
source). The `Prop` is the positive answer. -/
def WhiteheadAsphericity : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] (C : Set X) [Topology.CWComplex C],
    (∀ n, 2 < n → IsEmpty (Topology.CWComplex.cell C n)) → IsAspherical C →
    ∀ E : Topology.RelCWComplex.Subcomplex C, IsConnected (E : Set X) →
      IsAspherical (E : Set X)

end Whitehead

/-! ## Charney–Davis conjecture (rank 496) -/

section CharneyDavis

variable {m : ℕ}

/-- A finite abstract simplicial complex on the vertex set `Fin m`: a nonempty down-closed family
of finite sets (the empty face included, as is standard for `h`-vectors and reduced homology). -/
def IsComplex (L : Finset (Finset (Fin m))) : Prop :=
  ∅ ∈ L ∧ ∀ σ ∈ L, ∀ τ ⊆ σ, τ ∈ L

/-- Flag: every set of vertices that are pairwise joined by edges is a face. -/
def IsFlag (L : Finset (Finset (Fin m))) : Prop :=
  ∀ S : Finset (Fin m), (∀ v ∈ S, ∀ w ∈ S, ({v, w} : Finset (Fin m)) ∈ L) → S ∈ L

/-- The link `lk_L σ = {τ ∈ L | τ ∩ σ = ∅, τ ∪ σ ∈ L}`. -/
def link (L : Finset (Finset (Fin m))) (σ : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  L.filter fun τ => Disjoint τ σ ∧ τ ∪ σ ∈ L

/-- Simplicial chains supported on the faces of `L` with exactly `j` vertices (degree `j - 1`;
`j = 0` is the augmentation degree `-1` of reduced homology). -/
def chains (F : Type) [Field F] (L : Finset (Finset (Fin m))) (j : ℕ) :
    Submodule F (Finset (Fin m) → F) where
  carrier := {c | ∀ σ, c σ ≠ 0 → σ ∈ L ∧ σ.card = j}
  add_mem' {a b} ha hb σ h := by
    by_cases h1 : a σ = 0
    · exact hb σ (by simpa [h1] using h)
    · exact ha σ h1
  zero_mem' σ h := (h rfl).elim
  smul_mem' r c hc σ h := hc σ (by intro h0; exact h (by simp [h0]))

/-- The simplicial boundary with the vertex order of `Fin m`:
`(∂c)(τ) = Σ_{v ∉ τ} (-1)^{#{w ∈ τ | w < v}} c(τ ∪ {v})`, i.e. the face of `σ` omitting its
`k`-th vertex gets sign `(-1)^k`. -/
def boundary (F : Type) [Field F] : (Finset (Fin m) → F) →ₗ[F] (Finset (Fin m) → F) where
  toFun c τ := ∑ v ∈ Finset.univ \ τ, (-1 : F) ^ (τ.filter (· < v)).card * c (insert v τ)
  map_add' a b := by
    funext τ; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext τ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Reduced Betti number `dim_F H̃_{j-1}(L; F) = dim Z − dim B` (cycles minus boundaries). -/
noncomputable def reducedBetti (F : Type) [Field F] (L : Finset (Finset (Fin m))) (j : ℕ) : ℕ :=
  Module.finrank F (chains F L j ⊓ LinearMap.ker (boundary F) : Submodule F _) -
    Module.finrank F ((chains F L (j + 1)).map (boundary F))

/-- `L` is a *generalized homology `(N-1)`-sphere* (`N` = number of vertices of a top face):
for every face `σ` (including `σ = ∅`, whose link is `L`) and every field `F`, the link of `σ`
has the reduced `F`-homology of the sphere `S^{N-1-|σ|}` (for `|σ| = N` this is `S^{-1} = ∅`,
i.e. `H̃_{-1} = F`).

Fidelity notes: Charney–Davis use integral homology. For a finite complex, by the universal
coefficient theorem the integral reduced homology is that of a sphere iff the `F`-homology is,
for `F = ℚ` and every `F = 𝔽_p`, iff it is for every field; so quantifying over all fields
(in `Type`) is equivalent. The condition for nonempty `σ` makes `L` a homology manifold and
forces `dim L = N - 1`. -/
def IsGenHomologySphere (L : Finset (Finset (Fin m))) (N : ℕ) : Prop :=
  IsComplex L ∧ ∀ (F : Type) [Field F], ∀ σ ∈ L, ∀ j : ℕ,
    reducedBetti F (link L σ) j = if j + σ.card = N then 1 else 0

/-- The `h`-polynomial of a complex with top faces of `N` vertices:
`h(t) = Σ_{σ ∈ L} t^{|σ|} (1-t)^{N-|σ|} = Σ_i f_{i-1} t^i (1-t)^{N-i}`. -/
noncomputable def hPoly (L : Finset (Finset (Fin m))) (N : ℕ) : Polynomial ℤ :=
  ∑ σ ∈ L, Polynomial.X ^ σ.card * (1 - Polynomial.X) ^ (N - σ.card)

/-- **Rank 496 (open).** ProofAtlas exactTarget: "For every flag triangulation L of a
(2d-1)-dimensional generalized homology sphere, prove that (-1)^d times the value at -1 of its
h-polynomial is nonnegative."

Modelling: finite abstract simplicial complexes on `Fin m` (every finite complex is isomorphic
to one), flagness `IsFlag`, generalized homology `(2d-1)`-spheres `IsGenHomologySphere L (2d)`
(field-coefficient formulation, equivalent to the integral one — see that docstring), and the
`h`-polynomial `hPoly L (2d)`. -/
def CharneyDavisConjecture : Prop :=
  ∀ (m d : ℕ) (L : Finset (Finset (Fin m))), IsFlag L → IsGenHomologySphere L (2 * d) →
    0 ≤ (-1 : ℤ) ^ d * (hPoly L (2 * d)).eval (-1)

end CharneyDavis

/-! ## SHGH conjecture (rank 425) -/

section SHGH

open MvPolynomial

/-- `∂^l = ∂_{l₁} ∘ ⋯ ∘ ∂_{l_k}` on `ℂ[x₀,x₁,x₂]`. -/
noncomputable def iterDeriv (l : List (Fin 3)) :
    MvPolynomial (Fin 3) ℂ →ₗ[ℂ] MvPolynomial (Fin 3) ℂ :=
  l.foldr (fun i D => (pderiv i).toLinearMap ∘ₗ D) LinearMap.id

/-- The vector space of degree-`d` forms on `ℙ²` vanishing to order `≥ mᵢ` at the points
`[pᵢ]` (all partial derivatives of order `< mᵢ` vanish at `pᵢ`; for forms this is equivalent to
multiplicity `≥ mᵢ` at `[pᵢ]` by Euler's formula). -/
noncomputable def vanishSpace (d r : ℕ) (mult : Fin r → ℕ) (p : Fin r → Fin 3 → ℂ) :
    Submodule ℂ (MvPolynomial (Fin 3) ℂ) :=
  homogeneousSubmodule (Fin 3) ℂ d ⊓
    ⨅ i, ⨅ l : {l : List (Fin 3) // l.length < mult i},
      LinearMap.ker ((aeval (p i)).toLinearMap ∘ₗ iterDeriv l.1)

/-- Dimension (as a vector space, i.e. projective dimension `+ 1`) of the linear system
`L_d(m₁,…,m_r)` with base points in general position: the minimum over all point
configurations. Since the dimension is upper semicontinuous in the points on the irreducible
variety of configurations, this minimum is exactly the value at general points. -/
noncomputable def generalDim (d r : ℕ) (mult : Fin r → ℕ) : ℕ :=
  ⨅ p : {p : Fin r → Fin 3 → ℂ // ∀ i, p i ≠ 0}, Module.finrank ℂ (vanishSpace d r mult p.1)

/-- Expected (vector-space) dimension `max(0, C(d+2,2) − Σ C(mᵢ+1,2))`. -/
def expectedDim (d r : ℕ) (mult : Fin r → ℕ) : ℤ :=
  max 0 (((d + 2).choose 2 : ℤ) - ∑ i, ((mult i + 1).choose 2 : ℤ))

/-- Multiplicities padded by zeros. -/
def multPad {r : ℕ} (mult : Fin r → ℕ) (k : ℕ) : ℕ := if h : k < r then mult ⟨k, h⟩ else 0

/-- **Rank 425 (open).** ProofAtlas exactTarget: "Prove that a linear system of plane curves in
P^2 with base points in general position is special if and only if its fixed locus contains a
multiple (-1)-curve; equivalently, every Cremona-reduced such linear system is non-special."

Modelling: the second ("Cremona-reduced") formulation, stated in the exactTarget as equivalent;
the first needs `(-1)`-curves on blow-ups of `ℙ²` and fixed loci, which Mathlib lacks.
Cremona-reduced (standard form): `m₁ ≥ ⋯ ≥ m_r ≥ 0` and `d ≥ m₁ + m₂ + m₃` (missing
multiplicities read as `0` when `r < 3`). Non-special: the dimension at general points equals the
expected dimension `max(0, C(d+2,2) − Σ C(mᵢ+1,2))` (vector-space dimensions; empty systems
count as dimension `0`). Over `ℂ`; points are nonzero vectors of `ℂ³`; general position is the
minimum over configurations (`generalDim`). -/
def SHGHConjecture : Prop :=
  ∀ (d r : ℕ) (mult : Fin r → ℕ), Antitone mult →
    multPad mult 0 + multPad mult 1 + multPad mult 2 ≤ d →
    (generalDim d r mult : ℤ) = expectedDim d r mult

end SHGH

#print axioms artin_of_not_isOfFinOrder
#print axioms artinAllTwo_comm
#print axioms auslander_dim_one

end CryptoLean.OpenProblems.GeometryTopology.CombinatorialAlgebraic
