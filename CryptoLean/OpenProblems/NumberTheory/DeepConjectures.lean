import Mathlib

/-!
# Deep conjectures in number theory and arithmetic geometry

ProofAtlas problems (releaseRank) 7, 23, 28, 35, 37, 42, 44, 45, 47, 51, 58, 59, 61, 65, 74,
79, 80, 81, 82, 84, 89, 100, 107, 121, 128, 129, 130, 137, 142, 147, 150, 152, 161, 164, 175,
176, 183, 186, 197, 201, 202, 216, 218, 247, 258, 273, 283, 304, 305, 313, 334, 367, 368, 385,
389, 413, 424, 427, 430, 489.

**None of these problems is resolved here.**  ProofAtlas lists them as open, except that rank
283 (Mazur's real-topology conjecture) is listed as `claimed_pending_refereeing` (a claimed
answer not yet refereed) and ranks 35, 142, 218, 273 and 368 as `open_with_solved_subcases`
(open in general, with some special cases settled).  Nothing in this file proves, or claims
progress towards, any of them.  A problem whose statement can be written faithfully with objects that
Mathlib already has appears as an unproved `def … : Prop` whose docstring quotes the
ProofAtlas `exactTarget` and lists each modelling choice.  For every other problem the table
below names the Mathlib objects that are missing; no weaker substitute `Prop` is given for it.

## Stated here as `Prop`s

| rank | problem | declaration |
|------|---------|-------------|
| 161 | Keating–Snaith moments | `KeatingSnaithConjecture` |
| 183 | Lehmer's Mahler measure problem | `LehmerConjecture` (and `LehmerSequenceAlternative`) |
| 197 | Zagier's MZV dimension conjecture | `ZagierDimensionConjecture` |
| 202 | Shafarevich freeness over `ℚ^ab` | `ShafarevichFreenessConjecture` |
| 258 | Montgomery large values | `MontgomeryLargeValueConjecture` |
| 304 | Hilbert's tenth problem over `ℂ(t)` | `H10OverCtDecidable` |
| 368 | Greenberg's conjecture (bounded-class-number form) | `GreenbergConjecture` |

Problem 218 (dynamical Mordell–Lang) is **not** stated faithfully: Mathlib has no
quasi-projective varieties.  Its affine special case, itself an open problem, is recorded
separately as `DynamicalMordellLangAffine`, clearly labelled as a special case.

## Not expressible in current Mathlib (missing objects)

| rank | problem | missing Mathlib objects |
|------|---------|-------------------------|
| 7 | Global Langlands functoriality | reductive groups over number fields, L-groups and L-homomorphisms, adele groups `G(𝔸_F)`, automorphic representations, Satake parameters |
| 23 | Generalized Hodge conjecture | singular cohomology of complex varieties, rational Hodge structures, coniveau filtration |
| 28 | Generalized Ramanujan for `GL_n` | cuspidal automorphic representations of `GL_n(𝔸_F)`, local components, temperedness |
| 35 | Kronecker's Jugendtraum (Hilbert 12) | not a mathematical proposition: it asks for an explicit construction ("explicitly defined analytic functions"), which has no formal statement |
| 37 | Modularity over number fields (`End = ℤ`) | cohomology of adelic locally symmetric spaces, local Langlands `rec_{K_v}`, Weil–Deligne representations of elliptic curves over `K_v` |
| 42 | Fontaine–Mazur | `ℓ`-adic étale cohomology of varieties, de Rham `p`-adic Galois representations (`B_dR`) |
| 44 | Standard conjecture D | Weil cohomology theories, algebraic cycles with rational coefficients, numerical/homological equivalence |
| 45 | Grothendieck period conjecture | Nori motives, motivic Galois groups, period matrices |
| 47 | Equivariant Tamagawa number conjecture | motives with coefficients, motivic cohomology, Burns–Flach refined Euler characteristics, relative `K_0` |
| 51 | Bombieri–Lang | varieties of general type (Kodaira dimension), Zariski density of `X(K)` in a variety |
| 58 | Vojta's main conjecture | Weil heights and proximity functions on varieties, canonical divisors, SNC divisors |
| 59 | Modularity over totally real fields | Hilbert modular newforms, Hasse–Weil `L`-functions of elliptic curves over number fields |
| 61 | Artin holomorphy conjecture | Artin `L`-functions of Galois representations (and their continuation) |
| 65 | Deligne's critical-value conjecture | pure motives with coefficients, Betti/de Rham realizations and periods `c^±`, motivic `L`-functions |
| 74 | Weight–monodromy | `ℓ`-adic étale cohomology over local fields, monodromy operator, Weil–Deligne weight filtration |
| 79 | Zilber–Pink | mixed Shimura varieties and their special subvarieties |
| 80 | Campana's special varieties | sheaves of `p`-forms, Kodaira dimension of subsheaves, Campana core |
| 81 | Absolute Hodge conjecture | algebraic de Rham cohomology with comparison isomorphisms, Hodge classes, conjugate varieties `X^σ` |
| 82 | Grothendieck–Teichmüller | Drinfeld's profinite group `\widehat{GT}`, the Ihara embedding, profinite free group on two generators with its `GT`-action |
| 84 | Mumford–Tate for abelian varieties | abelian varieties over number fields, Tate modules with Galois action, Mumford–Tate groups |
| 87 | Effective Mordell (explicit height bound or terminating algorithm for X(K), genus ≥ 2) | smooth projective curves over number fields as varieties with their K-points and genus (Mathlib has schemes but no genus or Faltings finiteness), Weil/naive heights on such curves, Faltings' theorem itself. (Not assigned in the original grouping; row added afterwards. A hyperelliptic-only special case would be an unfaithful substitute, so none is stated.) |
| 89 | Section conjecture | étale fundamental groups of curves over number fields and the fundamental exact sequence |
| 100 | Selberg 1/4 | Laplace–Beltrami operator on `Γ\ℍ`, its `L²` spectrum for congruence subgroups |
| 107 | Grothendieck–Katz `p`-curvature | algebraic vector bundles with integrable connection, `p`-curvature, spreading out |
| 121 | Generalized Sato–Tate | Sato–Tate groups of abelian varieties, normalized Frobenius classes, Haar equidistribution on them |
| 128 | Global Gan–Gross–Prasad | classical groups over number fields, automorphic periods, Bessel/Fourier–Jacobi models, automorphic `L`-functions |
| 129 | `GL_n` subconvexity | standard `L`-functions of automorphic representations, analytic conductor |
| 130 | Murre's Chow–Künneth conjectures | Chow groups, correspondences, Betti cohomology of complex varieties |
| 137 | Colliot-Thélène (rationally connected) | rationally connected varieties, cohomological Brauer group `H²_et(X, 𝔾_m)`, Brauer–Manin set |
| 142 | Leopoldt | `p`-adic logarithm on `ℂ_p`-embeddings of units, `p`-adic regulator (or: `ℤ_p`-closure of global units in local unit groups).  A finite-level reformulation exists (the image of the global units in `∏_{v∣p} U_v^1/(U_v^1)^{p^m}` has order `≍ p^{m(r_1+r_2-1)}`), and Mathlib has the completions `K_v` and the unit rank; it is not used because its equivalence with the quoted defect/regulator target is not in the exactTarget and would itself need the `ℤ_p`-rank theory that is missing, so a `Prop` in that form would be an unverified substitute |
| 147 | Tate's Stark conjecture | Artin `L`-functions `L_S(s, χ)` and their leading terms at `0`, Stark regulators |
| 150 | Voevodsky smash-nilpotence | Chow groups with rational coefficients, exterior products of cycles |
| 152 | Manin's conjecture | Fano varieties, anticanonical heights, Picard rank |
| 164 | Kimura–O'Sullivan finite-dimensionality | the category of Chow motives, exterior and symmetric powers in it |
| 175 | Rank-one abelian Stark | partial zeta functions `ζ_{K/F,S}(σ, s)` and their continuation to `s = 0` |
| 176 | Simpson motivicity | local systems on complex quasi-projective varieties, rigidity in character varieties, Gauss–Manin systems |
| 186 | Brauer–Manin for curves of genus ≥ 2 | adelic points of curves, cohomological Brauer group, local invariants `inv_v` |
| 201 | Parshin conjecture | Quillen higher algebraic `K`-theory of schemes |
| 216 | Breuil–Mézard | potentially semistable deformation rings, Hilbert–Samuel multiplicities, Serre weights |
| 247 | Zagier's conjecture on `ζ_F(k)` | continued Dedekind zeta values `ζ_F(k)`, Zagier–Gangl allowable symbols `A_k(F)`, single-valued polylogarithms |
| 273 | Iwasawa `μ = 0` | cyclotomic `ℤ_p`-extensions, Iwasawa algebra modules and their `μ`-invariant.  An elementary class-number formulation does exist: by Iwasawa's formula `ord_p h(F_n) = μ p^n + λ n + ν` for `n ≫ 0`, so `μ = 0` iff `ord_p h(F_n) = O(n)`, which could be written with `NumberField.classNumber` and the layers used in `GreenbergConjecture`.  It is not used because, unlike rank 368, the exactTarget does not state that equivalence, and Iwasawa's formula is not in Mathlib, so the substitute could not be checked against the quoted target |
| 283 | Mazur's real-topology conjecture | algebraic varieties over `ℚ` with their real-analytic topology on `V(ℝ)` (only affine pieces are available, and closure in `V(ℝ)` is not local) |
| 305 | Igusa's monodromy conjecture | meromorphic continuation of Igusa zeta functions, Milnor fibre local monodromy |
| 313 | Brauer–Manin for K3 surfaces | K3 surfaces, cohomological Brauer group, adelic points |
| 334 | Coleman–Oort | moduli of ppav `A_g`, Torelli locus, Shimura subvarieties |
| 367 | Colmez conjecture | Faltings height, CM abelian varieties, Artin `L`-functions of CM types |
| 385 | Potential density on K3 surfaces | K3 surfaces over number fields, Zariski density of `X(L)` |
| 389 | Zariski dense orbit | rational self-maps of quasi-projective varieties, invariant rational functions `K(X)^f` |
| 413 | Dynamical Manin–Mumford | polarizable endomorphisms of projective varieties, ample line bundles and pull-back |
| 424 | Bounded negativity | complex projective surfaces, intersection pairing of curves |
| 427 | Kawaguchi–Silverman | Weil heights on varieties over `ℚ̄`, dynamical degrees `δ_1(f)` of rational maps |
| 430 | Beauville–Voisin | hyperkähler varieties, Chow rings, Chern classes, cycle class map |
| 489 | Birch–Tate | Milnor `K_2(𝒪_F)`, continued Dedekind zeta value `ζ_F(-1)` |

## Known results proved here

* `not_lehmerConjecture_iff`: the two alternatives of problem 183 are exactly complementary.
* `exists_mahlerMeasure_gap_of_natDegree_le`: Lehmer's gap holds for each fixed degree bound
  (a consequence of Northcott's theorem, `Polynomial.finite_mahlerMeasure_le`).
* `mahlerMeasure_cyclotomic`: cyclotomic polynomials have Mahler measure `1` (Mathlib's
  `Polynomial.cyclotomic_mahlerMeasure_eq_one`), so the hypothesis `M(P) > 1` in Lehmer's
  problem is not vacuous to drop.
* `zagier_dim_low_weights`: `dim_ℚ Z_k = d_k` for `k = 0, 1, 2` (the weight-2 case is
  `ζ(2) ≠ 0`).
-/

namespace CryptoLean.OpenProblems.NumberTheory.DeepConjectures

open Polynomial Filter Topology

/-! ## Problem 183: Lehmer's Mahler measure problem -/

/-- The Mahler measure of an integer polynomial, computed (as in Mathlib) after mapping it to
`ℂ[X]`: `M(P) = |a_d| ∏ max(1, |α_i|)`. -/
noncomputable abbrev intMahler (P : ℤ[X]) : ℝ :=
  (P.map (Int.castRingHom ℂ)).mahlerMeasure

/-- **Open problem (ProofAtlas rank 183, Lehmer's problem), first alternative.**

ProofAtlas exactTarget: "Prove that there exists an absolute epsilon > 0 such that every monic
integer polynomial P with Mahler measure M(P) > 1 satisfies M(P) >= 1 + epsilon, or construct a
sequence of such polynomials whose Mahler measures decrease to 1."

This `Prop` is the first alternative (Lehmer's conjecture).  The second alternative is
`LehmerSequenceAlternative`; `not_lehmerConjecture_iff` proves they are exact complements, so
the problem asks which of the two holds.

Modelling: Mahler measure is Mathlib's `Polynomial.mahlerMeasure` of the image in `ℂ[X]`. -/
def LehmerConjecture : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ P : ℤ[X], P.Monic → 1 < intMahler P → 1 + ε ≤ intMahler P

/-- The second alternative of ProofAtlas problem 183: a sequence of monic integer polynomials
with Mahler measures `> 1` that strictly decrease to `1`. -/
def LehmerSequenceAlternative : Prop :=
  ∃ P : ℕ → ℤ[X], (∀ n, (P n).Monic ∧ 1 < intMahler (P n)) ∧
    StrictAnti (fun n => intMahler (P n)) ∧
    Tendsto (fun n => intMahler (P n)) atTop (𝓝 1)

/-- **Known result** (elementary logic/analysis; the dichotomy in Lehmer 1933's question):
Lehmer's conjecture fails exactly when there is a sequence of monic integer polynomials with
Mahler measures `> 1` strictly decreasing to `1`. -/
theorem not_lehmerConjecture_iff : ¬ LehmerConjecture ↔ LehmerSequenceAlternative := by
  constructor
  · intro h
    have h' : ∀ ε : ℝ, 0 < ε → ∃ P : ℤ[X], P.Monic ∧ 1 < intMahler P ∧ intMahler P < 1 + ε := by
      intro ε hε
      by_contra hc
      push Not at hc
      exact h ⟨ε, hε, fun P hP h1 => hc P hP h1⟩
    choose g hg using h'
    let g' : ℝ → ℤ[X] := fun ε => if hε : 0 < ε then g ε hε else 0
    have hg' : ∀ ε, 0 < ε → (g' ε).Monic ∧ 1 < intMahler (g' ε) ∧ intMahler (g' ε) < 1 + ε := by
      intro ε hε
      simp only [g', hε, dite_true]
      exact hg ε hε
    let f : ℕ → ℤ[X] := fun n => Nat.rec (g' 1)
      (fun k Pk => g' (min (intMahler Pk - 1) (1 / ((k : ℝ) + 2)))) n
    have hf0 : f 0 = g' 1 := rfl
    have hfs : ∀ k, f (k + 1) = g' (min (intMahler (f k) - 1) (1 / ((k : ℝ) + 2))) :=
      fun k => rfl
    have key : ∀ n, (f n).Monic ∧ 1 < intMahler (f n) ∧
        intMahler (f n) < 1 + 1 / ((n : ℝ) + 1) := by
      intro n
      induction n with
      | zero => rw [hf0]; simpa using hg' 1 one_pos
      | succ k ih =>
        rw [hfs]
        have hpos : 0 < min (intMahler (f k) - 1) (1 / ((k : ℝ) + 2)) :=
          lt_min (by linarith [ih.2.1]) (by positivity)
        obtain ⟨a, b, c⟩ := hg' _ hpos
        refine ⟨a, b, ?_⟩
        have := min_le_right (intMahler (f k) - 1) (1 / ((k : ℝ) + 2))
        have e2 : (1:ℝ) / ((k:ℝ) + 2) = 1 / (((k + 1 : ℕ) : ℝ) + 1) := by push_cast; ring
        linarith
    have hdec : ∀ k, intMahler (f (k + 1)) < intMahler (f k) := by
      intro k
      rw [hfs]
      have hpos : 0 < min (intMahler (f k) - 1) (1 / ((k : ℝ) + 2)) :=
        lt_min (by linarith [(key k).2.1]) (by positivity)
      have := (hg' _ hpos).2.2
      have := min_le_left (intMahler (f k) - 1) (1 / ((k : ℝ) + 2))
      linarith
    refine ⟨f, fun n => ⟨(key n).1, (key n).2.1⟩, strictAnti_nat_of_succ_lt hdec, ?_⟩
    have hlim : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => (key n).2.1.le) (fun n => (key n).2.2.le)
  · rintro ⟨P, hP, -, hlim⟩ ⟨ε, hε, hL⟩
    have hev : ∀ᶠ n in atTop, intMahler (P n) < 1 + ε :=
      hlim.eventually (gt_mem_nhds (by linarith))
    obtain ⟨n, hn⟩ := hev.exists
    linarith [hL (P n) (hP n).1 (hP n).2]

/-- **Known result** (Northcott 1949; Mathlib's `Polynomial.finite_mahlerMeasure_le`): for each
degree bound `n` there is a gap `ε_n > 0` above `1` in the Mahler measures of integer
polynomials of degree at most `n`.  (Lehmer's problem asks for a gap independent of `n`; this
degree-dependent statement is not progress on it.) -/
theorem exists_mahlerMeasure_gap_of_natDegree_le (n : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P : ℤ[X], P.natDegree ≤ n → 1 < intMahler P → 1 + ε ≤ intMahler P := by
  have hfin := finite_mahlerMeasure_le n 2
  let F : Finset ℝ :=
    (hfin.toFinset.filter (fun P => 1 < intMahler P)).image (fun P => intMahler P - 1) ∪ {1}
  have hne : F.Nonempty := ⟨1, by simp [F]⟩
  have hFpos : ∀ x ∈ F, 0 < x := by
    intro x hx
    simp only [F, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_singleton] at hx
    rcases hx with ⟨P, ⟨-, hP⟩, rfl⟩ | rfl
    · linarith
    · norm_num
  refine ⟨F.min' hne, hFpos _ (F.min'_mem hne), fun P hdeg h1 => ?_⟩
  by_cases h2 : intMahler P ≤ 2
  · have hmem : intMahler P - 1 ∈ F := by
      simp only [F, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset]
      left
      exact ⟨P, ⟨⟨hdeg, by exact_mod_cast h2⟩, h1⟩, rfl⟩
    have := F.min'_le _ hmem
    linarith
  · have := F.min'_le 1 (by simp [F])
    push Not at h2
    linarith

/-- **Known result** (Kronecker 1857; Mathlib's `Polynomial.cyclotomic_mahlerMeasure_eq_one`):
every cyclotomic polynomial has Mahler measure exactly `1`. -/
theorem mahlerMeasure_cyclotomic (m : ℕ) : intMahler (cyclotomic m ℤ) = 1 :=
  cyclotomic_mahlerMeasure_eq_one (R := ℤ) m

/-! ## Problem 197: Zagier's dimension conjecture for multiple zeta values -/

/-- The classical multiple zeta value `ζ(k_1, …, k_r) = ∑_{n_1 > ⋯ > n_r > 0} ∏ n_i^{-k_i}`,
written as an unconditional sum (`tsum`) over strictly decreasing tuples of positive integers.
For admissible indices (`k_i ≥ 1`, `k_1 ≥ 2`) the series converges absolutely, so this is the
classical value. -/
noncomputable def mzv (k : List ℕ) : ℝ :=
  ∑' n : {n : Fin k.length → ℕ // StrictAnti n ∧ ∀ i, 0 < n i},
    ∏ i, (((n.1 i : ℕ) : ℝ) ^ k.get i)⁻¹

/-- Admissible indices of weight `w`: positive integers `k_1, …, k_r` with `k_1 ≥ 2` and sum
`w`.  (The empty index is not admissible here; weight `0` is handled separately.) -/
def Admissible (w : ℕ) (k : List ℕ) : Prop :=
  (∀ x ∈ k, 1 ≤ x) ∧ k.sum = w ∧ 2 ≤ k.headD 0

/-- `Z_w`: the `ℚ`-span of the multiple zeta values of weight `w`, with `Z_0 = ℚ·1`.  For
`w = 1` there are no admissible indices, so `Z_1 = {0}` automatically. -/
noncomputable def mzvSpan (w : ℕ) : Submodule ℚ ℝ :=
  if w = 0 then Submodule.span ℚ {1} else Submodule.span ℚ (mzv '' {k | Admissible w k})

/-- Zagier's numbers: `d_0 = 1, d_1 = 0, d_2 = 1, d_k = d_{k-2} + d_{k-3}`. -/
def zagierD : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | (n + 3) => zagierD (n + 1) + zagierD n

/-- **Open problem (ProofAtlas rank 197, Zagier's dimension conjecture).**

ProofAtlas exactTarget: "For positive integers k_1,...,k_r with k_1>=2, define the classical
convergent real multiple zeta value zeta(k_1,...,k_r)=sum_(n_1>...>n_r>0) 1/(n_1^k_1 ...
n_r^k_r), of weight k_1+...+k_r. For each k>=2 let Z_k be their Q-linear span at weight k, with
Z_0=Q generated by the empty value1 and Z_1={0}. Define d_0=1,d_1=0,d_2=1 and
d_k=d_(k-2)+d_(k-3) for k>=3. Is dim_Q Z_k=d_k for every k>=0?"

Modelling: `mzv` is a `tsum` (absolutely convergent for admissible indices); `Z_k` is
`mzvSpan k`, a `ℚ`-submodule of `ℝ`; `dim_ℚ` is `Module.finrank`.  `Z_k` is spanned by the
finitely many admissible indices of weight `k`, so it is finite-dimensional and `finrank` is the
true dimension.  The upper bound `dim Z_k ≤ d_k` is a theorem (Terasoma, Deligne–Goncharov);
the conjecture is the equality. -/
def ZagierDimensionConjecture : Prop :=
  ∀ k : ℕ, Module.finrank ℚ (mzvSpan k) = zagierD k

private theorem mzvSpan_of_ne {w : ℕ} (hw : w ≠ 0) :
    mzvSpan w = Submodule.span ℚ (mzv '' {k | Admissible w k}) := by
  simp [mzvSpan, hw]

private theorem admissible_two (k : List ℕ) : Admissible 2 k ↔ k = [2] := by
  constructor
  · rintro ⟨hpos, hsum, hhead⟩
    match k, hpos, hsum, hhead with
    | [], _, _, h => simp at h
    | [a], _, hs, _ => simpa using hs
    | a :: b :: rest, hp, hs, hh =>
      simp only [List.headD_cons] at hh
      have hb : 1 ≤ b := hp b (by simp)
      simp only [List.sum_cons] at hs
      omega
  · rintro rfl
    exact ⟨by simp, by simp, by simp⟩

private theorem mzv_two_pos : 0 < mzv [2] := by
  unfold mzv
  have hsub : ∀ i j : Fin [2].length, i = j := fun i j =>
    Fin.ext (by have := i.2; have := j.2; simp only [List.length_singleton] at *; omega)
  let e : {n : Fin [2].length → ℕ // StrictAnti n ∧ ∀ i, 0 < n i} ≃ {m : ℕ // 0 < m} :=
    { toFun := fun n => ⟨n.1 0, n.2.2 0⟩
      invFun := fun m => ⟨fun _ => m.1, fun i j hij => absurd hij (by
        rw [hsub i j]; exact lt_irrefl _), fun _ => m.2⟩
      left_inv := by
        intro n
        apply Subtype.ext
        funext i
        have : i = 0 := hsub _ _
        subst this; rfl
      right_inv := by intro m; rfl }
  have hterm : ∀ n : {n : Fin [2].length → ℕ // StrictAnti n ∧ ∀ i, 0 < n i},
      (∏ i, (((n.1 i : ℕ) : ℝ) ^ [2].get i)⁻¹) = (((e n : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro n
    simp [e]
  simp_rw [hterm]
  have hsum : Summable (fun m : {m : ℕ // 0 < m} => (((m : ℕ) : ℝ) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    exact (h.subtype (fun m : ℕ => 0 < m)).congr (fun m => by simp)
  have hsum' : Summable (fun n => (((e n : ℕ) : ℝ) ^ 2)⁻¹) :=
    (e.summable_iff (f := fun m : {m : ℕ // 0 < m} => (((m : ℕ) : ℝ) ^ 2)⁻¹)).mpr hsum
  exact hsum'.tsum_pos (fun _ => by positivity) (e.symm ⟨1, one_pos⟩) (by rw [e.apply_symm_apply]; norm_num)

/-- **Known result** (conventions for `k = 0, 1`; for `k = 2`, `ζ(2) = π²/6 ≠ 0`, Euler 1734):
Zagier's formula `dim_ℚ Z_k = d_k` holds for `k = 0, 1, 2`.  This is a finite check of three
small weights, not progress on the conjecture for all `k`. -/
theorem zagier_dim_low_weights :
    ∀ k ≤ 2, Module.finrank ℚ (mzvSpan k) = zagierD k := by
  intro k hk
  interval_cases k
  · simp only [mzvSpan, zagierD]
    exact finrank_span_singleton one_ne_zero
  · have : {k : List ℕ | Admissible 1 k} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hpos, hsum, hhead⟩
      match k, hpos, hsum, hhead with
      | [], _, _, h => simp at h
      | a :: rest, _, hs, hh =>
        simp only [List.headD_cons, List.sum_cons] at hh hs
        omega
    rw [mzvSpan_of_ne one_ne_zero, this, Set.image_empty, Submodule.span_empty]
    simp [zagierD]
  · have : {k : List ℕ | Admissible 2 k} = {[2]} := by
      ext k; simp [admissible_two]
    rw [mzvSpan_of_ne two_ne_zero, this, Set.image_singleton]
    exact finrank_span_singleton mzv_two_pos.ne'

/-! ## Problem 161: Keating–Snaith moments of `ζ` on the critical line -/

/-- The Barnes `G`-function in the form `z ↦ G(1 + z)` for real `z > -1`, by its Weierstrass
product
`G(1+z) = (2π)^{z/2} exp(-(z + (1+γ) z²)/2) ∏_{j ≥ 1} (1 + z/j)^j exp(z²/(2j) - z)`,
with `γ` the Euler–Mascheroni constant.  Mathlib has no Barnes `G`-function; this is the
standard definition (Barnes 1900).  The infinite product is Mathlib's `tprod`; it converges
absolutely (factors `1 + O(1/j²)`) for the positive real arguments used below. -/
noncomputable def barnesGOnePlus (z : ℝ) : ℝ :=
  (2 * Real.pi) ^ (z / 2) * Real.exp (-(z + (1 + Real.eulerMascheroniConstant) * z ^ 2) / 2) *
    ∏' j : ℕ, (1 + z / ((j : ℝ) + 1)) ^ (j + 1) * Real.exp (z ^ 2 / (2 * ((j : ℝ) + 1)) - z)

/-- The arithmetic factor
`a_k = ∏_p (1 - 1/p)^{k²} ∑_{m ≥ 0} (Γ(m+k)/(Γ(k) m!))² p^{-m}`. -/
noncomputable def keatingSnaithArith (k : ℝ) : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / (p : ℝ)) ^ (k ^ 2) *
    ∑' m : ℕ, (Real.Gamma (m + k) / (Real.Gamma k * (m.factorial : ℝ))) ^ 2 * (p : ℝ) ^ (-(m : ℝ))

/-- `I_k(T) = ∫_0^T |ζ(1/2 + it)|^{2k} dt`. -/
noncomputable def zetaMoment (k T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ‖riemannZeta (1 / 2 + t * Complex.I)‖ ^ (2 * k)

/-- **Open problem (ProofAtlas rank 161, Keating–Snaith conjecture).**

ProofAtlas exactTarget: "For every fixed real k>0, let I_k(T)=integral_0^T |zeta(1/2+it)|^(2k)
dt. Prove that I_k(T) is asymptotic to a_k G(1+k)^2/G(1+2k) times T(log T)^(k^2), where G is the
Barnes G-function and a_k=product_p (1-1/p)^(k^2) sum_(m>=0) (Gamma(m+k)/(Gamma(k)m!))^2 p^(-m)."

Modelling: `ζ` is Mathlib's `riemannZeta`; the Barnes `G`-function is `barnesGOnePlus`
(Weierstrass product, defined here since Mathlib lacks it); the Euler product and the series in
`a_k` are `tprod`/`tsum`; "asymptotic to" is `Asymptotics.IsEquivalent` as `T → ∞`.  Only
`k = 1` (Hardy–Littlewood) and `k = 2` (Ingham) are known; neither is proved here. -/
def KeatingSnaithConjecture : Prop :=
  ∀ k : ℝ, 0 < k →
    Asymptotics.IsEquivalent atTop (fun T => zetaMoment k T)
      (fun T => keatingSnaithArith k * barnesGOnePlus k ^ 2 / barnesGOnePlus (2 * k) * T *
        Real.log T ^ (k ^ 2))

/-! ## Problem 258: Montgomery's large value conjecture -/

/-- **Open problem (ProofAtlas rank 258, Montgomery's large value conjecture).**

ProofAtlas exactTarget: "For every fixed sigma > 1/2 and N <= T <= N^{O(1)}, prove that if
D(t) = sum_{N<n<=2N} b_n exp(it log n) has |b_n| <= 1 and W is a 1-separated subset of [0,T] on
which |D(t)| > N^sigma, then |W| <= C(sigma) T^{o(1)} N^{2-2sigma}."

Modelling: `N` is a positive integer; `N ≤ T ≤ N^{O(1)}` is `N ≤ T ≤ N^A` for an arbitrary
fixed `A ≥ 1`; `T^{o(1)}` is read as "for every `ε > 0`, `T^ε`", with the constant allowed to
depend on `σ`, `A` and `ε`; `W` is a finite set (a 1-separated subset of `[0,T]` is finite);
`b_n ∈ ℂ`. -/
def MontgomeryLargeValueConjecture : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → ∀ A : ℝ, 1 ≤ A → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    ∀ T : ℝ, (N : ℝ) ≤ T → T ≤ (N : ℝ) ^ A →
    ∀ b : ℕ → ℂ, (∀ n, ‖b n‖ ≤ 1) →
    ∀ W : Finset ℝ, (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) → (∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s|) →
    (∀ t ∈ W, (N : ℝ) ^ σ <
      ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
    (W.card : ℝ) ≤ C * T ^ ε * (N : ℝ) ^ (2 - 2 * σ)

/-! ## Problem 304: Hilbert's tenth problem over `ℂ(t)` -/

/-- Evaluation of an encoded polynomial `f ∈ ℤ[t][x_0, x_1, …]` at a point of `ℂ(t)`.  The
code is a finite list of monomials `(c, e)` with `c ∈ ℤ` and exponent list
`e = [e_t, e_0, e_1, …]`; the monomial is `c · t^{e_t} · ∏_i x_i^{e_i}`. -/
noncomputable def h10Eval (f : List (ℤ × List ℕ)) (x : ℕ → RatFunc ℂ) : RatFunc ℂ :=
  (f.map fun ce => ((ce.1 : RatFunc ℂ) * RatFunc.X ^ ce.2.headD 0) *
    (ce.2.tail.mapIdx fun i e => x i ^ e).prod).sum

/-- The encoded equation `f = 0` has a solution in `ℂ(t)`. -/
def H10CtSolvable (f : List (ℤ × List ℕ)) : Prop :=
  ∃ x : ℕ → RatFunc ℂ, h10Eval f x = 0

/-- **Open problem (ProofAtlas rank 304, Hilbert's tenth problem over `ℂ(t)`).**

ProofAtlas exactTarget: "Let t be a fixed transcendental indeterminate and C(t) the field of
complex rational functions. Determine whether there exists an algorithm (Turing machine) which,
given any n >= 1 and any polynomial f in Z[t][x_1,...,x_n], presented by its finite list of
integer coefficients and monomial exponents in t and the x_i, halts and correctly decides
whether f = 0 has a solution (x_1,...,x_n) in C(t)^n. …"

The problem asks whether this `Prop` or its negation holds; neither is known.

Modelling: "algorithm" is Mathlib's `ComputablePred` (partial recursive functions); inputs are
the finite coefficient/exponent lists described at `h10Eval`, with the number of variables `n`
implicit as the length of the exponent lists (variables not occurring may be assigned anything,
so a solution in `ℂ(t)^ℕ` is the same as one in `ℂ(t)^n`).  The equivalent model-theoretic
formulation quoted in the source is not separately formalised. -/
def H10OverCtDecidable : Prop :=
  ComputablePred H10CtSolvable

/-! ## Problem 202: Shafarevich's freeness conjecture -/

/-- `ℚ̄`, Mathlib's algebraic closure of `ℚ`. -/
abbrev Qbar : Type := AlgebraicClosure ℚ

/-- `ℚ^ab`, the maximal cyclotomic extension of `ℚ` inside `ℚ̄`: the subfield generated by all
roots of unity (equal to the maximal abelian extension by Kronecker–Weber). -/
noncomputable def Qab : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {x : Qbar | ∃ n : ℕ, 0 < n ∧ x ^ n = 1}

/-- A topological group is **free profinite of countably infinite rank** (on a basis converging
to `1`): it is profinite, and there is `ι : ℕ → G` with `ι n → 1` such that every map
`φ : ℕ → H` into a finite group that is eventually `1` extends uniquely along `ι` to a
continuous homomorphism (continuity into a discrete group = open kernel).  For profinite `G`,
the universal property against finite groups is equivalent to the one against all profinite
groups. -/
def IsFreeProfiniteOfCountableRank (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
  ∃ ι : ℕ → G, Tendsto ι atTop (𝓝 1) ∧
    ∀ (H : Type) [Group H] [Finite H] (φ : ℕ → H), (∀ᶠ n in atTop, φ n = 1) →
      ∃! ψ : G →* H, IsOpen (ψ.ker : Set G) ∧ ∀ n, ψ (ι n) = φ n

/-- **Open problem (ProofAtlas rank 202, Shafarevich's conjecture).**

ProofAtlas exactTarget: "Let Qab be the maximal abelian extension of Q in an algebraic closure
Qbar (equivalently the maximal cyclotomic extension). The absolute Galois group Gal(Qbar/Qab) is
a free profinite group of countably infinite rank, in the standard profinite convention of a free
basis converging to the identity."

Modelling: `ℚ̄ = AlgebraicClosure ℚ`; `ℚ^ab` is `Qab` (all roots of unity adjoined);
`Gal(ℚ̄/ℚ^ab)` is `Qbar ≃ₐ[Qab] Qbar` with Mathlib's Krull topology; freeness is
`IsFreeProfiniteOfCountableRank` (universal property against finite groups, basis indexed by
`ℕ` and converging to `1`). -/
def ShafarevichFreenessConjecture : Prop :=
  IsFreeProfiniteOfCountableRank (Qbar ≃ₐ[Qab] Qbar)

/-! ## Problem 368: Greenberg's conjecture (bounded `p`-parts of class numbers) -/

/-- `ℚ(μ_m)`, the `m`-th cyclotomic field, as the subfield of `ℚ̄` generated by the `m`-th
roots of unity. -/
noncomputable def cycloSub (m : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {x : Qbar | x ^ m = 1}

/-- The compositum of two number fields inside `ℚ̄` is a number field. -/
instance numberField_sup (F L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F]
    [FiniteDimensional ℚ L] : NumberField ↥(F ⊔ L) where

/-- **Open problem (ProofAtlas rank 368, Greenberg's conjecture), in the equivalent form the
exactTarget itself gives.**

ProofAtlas exactTarget: "Prove that for every totally real number field F and every prime p, the
Iwasawa invariants lambda_p(F) and mu_p(F) of the cyclotomic Z_p-extension vanish; equivalently,
the p-parts of class numbers in the tower remain bounded."

This `Prop` is the second ("equivalently") form: with `F_n` the `n`-th layer of the cyclotomic
`ℤ_p`-extension of `F`, there is `C` with `ord_p h(F_n) ≤ C` for all `n`.

Modelling:
1. Number fields are finite-dimensional subfields `F` of `ℚ̄ = AlgebraicClosure ℚ` (every number
   field embeds in `ℚ̄`, and being totally real and the class number are invariant under
   isomorphism); "totally real" is Mathlib's `NumberField.IsTotallyReal`.
2. The `n`-th layer `ℚ_n` of the cyclotomic `ℤ_p`-extension of `ℚ` is described as a subfield
   `L` of `ℚ(μ_m) = cycloSub m`, `m = p^{n+1}` (`m = 2^{n+2}` for `p = 2`), that is totally real
   and of degree `p^n` over `ℚ`.  Such an `L` exists and is unique (for odd `p` the Galois group
   `(ℤ/p^{n+1})^×` is cyclic; for `p = 2` the totally real subfields lie in `ℚ(ζ + ζ⁻¹)`, of
   degree `2^n`), so quantifying over all such `L` is the statement about `ℚ_n`; existence and
   uniqueness are classical and are not proved here.
3. `F_n = F·ℚ_n` is the compositum `F ⊔ L` in `ℚ̄`; the `p`-part of its class number is
   measured by `padicValNat p (NumberField.classNumber (F ⊔ L))`.
4. The equivalence with `λ_p(F) = μ_p(F) = 0` (Iwasawa's formula `ord_p h(F_n) = μ p^n + λ n + ν`
   for large `n`) is taken from the exactTarget; Iwasawa invariants are not in Mathlib, so the
   first form is not formalised separately. -/
def GreenbergConjecture : Prop :=
  ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F], NumberField.IsTotallyReal F →
  ∀ p : ℕ, p.Prime → ∃ C : ℕ, ∀ n : ℕ,
    ∀ (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L],
      L ≤ cycloSub (if p = 2 then 2 ^ (n + 2) else p ^ (n + 1)) →
      Module.finrank ℚ L = p ^ n → NumberField.IsTotallyReal L →
      padicValNat p (NumberField.classNumber ↥(F ⊔ L)) ≤ C

/-! ## Problem 218 (special case only): dynamical Mordell–Lang for affine space -/

/-- A set of natural numbers is a finite union of arithmetic progressions `{a + b m : m ≥ 0}`
(step `b = 0` allowed, giving singletons; the empty union gives `∅`). -/
def IsFiniteUnionOfAPs (S : Set ℕ) : Prop :=
  ∃ F : Finset (ℕ × ℕ), S = ⋃ p ∈ F, {n | ∃ m : ℕ, n = p.1 + p.2 * m}

/-- The polynomial self-map `x ↦ (F_1(x), …, F_N(x))` of `K^N`. -/
noncomputable def polyMap {K : Type*} [Field K] {N : ℕ} (F : Fin N → MvPolynomial (Fin N) K) :
    (Fin N → K) → (Fin N → K) :=
  fun x i => MvPolynomial.eval x (F i)

/-- **Open problem; a SPECIAL CASE of ProofAtlas rank 218 (dynamical Mordell–Lang), not the
ProofAtlas target itself.**

ProofAtlas exactTarget: "For every field K of characteristic zero, every quasiprojective variety
X over K, every K-morphism f:X->X, every closed K-subvariety V of X and every point x in X(K),
the set {n in Z_{≥0}: f^n(x) is in V(K)} is a finite union of arithmetic progressions
{a+bm:m in Z_{≥0}} with a,b nonnegative integers. …"

This `Prop` restricts `X` to affine varieties: since every affine variety is closed in some
`𝔸^N` and every morphism of an affine `X ⊆ 𝔸^N` extends to a polynomial self-map of `𝔸^N`
agreeing on `X`, it is equivalent to the case `X = 𝔸^N_K` stated below.  Simplifications:
(1) `X` affine (quasi-projective varieties are missing from Mathlib, so the full target is listed
as not expressible); (2) `V(K)` is the common zero set in `K^N` of an arbitrary set of
polynomials; (3) `K : Type` (universe 0).  The affine-space case is open in general for `N ≥ 3`; for `N = 2` it is known
over `ℚ̄` (Xie 2017), which does not by itself cover every characteristic-zero `K` quantified
here. -/
def DynamicalMordellLangAffine : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (N : ℕ) (F : Fin N → MvPolynomial (Fin N) K)
    (S : Set (MvPolynomial (Fin N) K)) (x : Fin N → K),
    IsFiniteUnionOfAPs {n : ℕ | ∀ g ∈ S, MvPolynomial.eval ((polyMap F)^[n] x) g = 0}

#print axioms not_lehmerConjecture_iff
#print axioms exists_mahlerMeasure_gap_of_natDegree_le
#print axioms mahlerMeasure_cyclotomic
#print axioms zagier_dim_low_weights

end CryptoLean.OpenProblems.NumberTheory.DeepConjectures
