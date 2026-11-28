import Mathlib

/-!
# Perfect secret sharing for general access structures, and the polynomial Hirsch question

Open problems (ProofAtlas list):
* #13 Polynomial-size perfect secret sharing -> `PolySizeSecretSharing` (OPEN, `def ... : Prop`).
* #12 Polynomial diameter bound for polytopes (polynomial Hirsch conjecture)
  -> `PolynomialHirsch` (OPEN, `def ... : Prop`).

Neither problem is resolved here. What is proved is the classical, known existence theorem for
general access structures (Ito–Saito–Nishizeki 1987; the "DNF" form of Benaloh–Leichter 1988):

* `Scheme.perfect_dnfScheme` (known result): for any family `F` of authorized sets that generates
  the access structure, XOR-sharing the secret bit independently among the members of every
  `C ∈ F` is a perfect (correct and private) scheme, with one bit per set of `F` per party;
* `exists_perfect_scheme` (known result): every access structure on `n` parties has a perfect
  one-bit scheme whose share is `ℓ` bits, where `ℓ` is the number of minimal authorized sets,
  and `ℓ ≤ choose n ⌊n/2⌋ ≤ 2 ^ n` (the bound on `ℓ` is Sperner's theorem, used as stated from
  Mathlib's `IsAntichain.sperner`).

The open question asks whether the exponential share size can be replaced by a polynomial in `n`.

## Model

* Parties are `Fin n`; an access structure is an up-closed family `A : Finset (Finset (Fin n))`
  with `∅ ∉ A` (`IsAccessStructure`).
* A scheme for a one-bit secret `s : ZMod 2` (`Scheme n Sh`) is a finite, nonempty randomness
  space `R`, sampled uniformly, and a dealing map `share : ZMod 2 → R → Fin n → Sh`.
* Perfect correctness (`Scheme.Correct`): for each authorized `B ∈ A`, the shares of `B`
  determine the secret, i.e. two dealings that agree on all shares of `B` have the same secret.
  (This is equivalent to the existence of a reconstruction function on `B`'s shares.)
* Perfect privacy (`Scheme.Private`): for each unauthorized `T ∉ A` and each possible view
  `v`, the number of `r : R` producing view `v` on `T` is the same for `s = 0` and `s = 1`.
  Since `r` is uniform on `R`, this says exactly that the distribution of `T`'s shares is the
  same for both secrets.

Modelling simplification (stated honestly): randomness is uniform on a finite set. Any finite
probability space with rational probabilities is the image of such a uniform space, so this is the
usual combinatorial formulation (Beimel, "Secret-sharing schemes: a survey", IWCC 2011, §2).
-/

namespace CryptoLean.OpenProblems.SecretSharing

open Finset

/-- An access structure on `n` parties: an up-closed family of subsets of `Fin n` not containing
the empty set (the empty coalition never learns the secret). -/
def IsAccessStructure {n : ℕ} (A : Finset (Finset (Fin n))) : Prop :=
  ∅ ∉ A ∧ ∀ B ∈ A, ∀ C : Finset (Fin n), B ⊆ C → C ∈ A

/-- A secret-sharing scheme for a one-bit secret among `n` parties with share space `Sh`:
a nonempty finite randomness space `R` (sampled uniformly) and the dealing map. -/
structure Scheme (n : ℕ) (Sh : Type) : Type 1 where
  /-- The randomness space of the dealer, sampled uniformly. -/
  R : Type
  [fintypeR : Fintype R]
  [nonemptyR : Nonempty R]
  /-- `share s r i` is the share of party `i` when the secret is `s` and the coins are `r`. -/
  share : ZMod 2 → R → Fin n → Sh

attribute [instance] Scheme.fintypeR Scheme.nonemptyR

namespace Scheme

variable {n : ℕ} {Sh Sh' : Type}

/-- Perfect correctness: the shares of every authorized set determine the secret. -/
def Correct (A : Finset (Finset (Fin n))) (S : Scheme n Sh) : Prop :=
  ∀ B ∈ A, ∀ (s s' : ZMod 2) (r r' : S.R),
    (∀ i ∈ B, S.share s r i = S.share s' r' i) → s = s'

/-- Perfect privacy: for every unauthorized set `T` and every view `v`, the number of coin
values producing view `v` on `T` is the same for secret `0` and secret `1`; with uniform coins
this is equality of the two share distributions of `T`. -/
def Private (A : Finset (Finset (Fin n))) (S : Scheme n Sh) : Prop :=
  ∀ T : Finset (Fin n), T ∉ A → ∀ v : Fin n → Sh,
    Nat.card {r : S.R // ∀ i ∈ T, S.share 0 r i = v i} =
      Nat.card {r : S.R // ∀ i ∈ T, S.share 1 r i = v i}

/-- A perfect secret-sharing scheme for `A`: perfectly correct and perfectly private. -/
def Perfect (A : Finset (Finset (Fin n))) (S : Scheme n Sh) : Prop :=
  S.Correct A ∧ S.Private A

/-- Re-encode the shares along a bijection of share spaces. -/
def mapShares (e : Sh ≃ Sh') (S : Scheme n Sh) : Scheme n Sh' where
  R := S.R
  share s r i := e (S.share s r i)

theorem perfect_mapShares (e : Sh ≃ Sh') {A : Finset (Finset (Fin n))} {S : Scheme n Sh}
    (h : S.Perfect A) : (S.mapShares e).Perfect A := by
  refine ⟨fun B hB s s' r r' hsh => h.1 B hB s s' r r' fun i hi => e.injective (hsh i hi), ?_⟩
  intro T hT v
  have := h.2 T hT (fun i => e.symm (v i))
  simpa [mapShares, ← Equiv.eq_symm_apply] using this

/-! ### The DNF / Ito–Saito–Nishizeki construction -/

section DNF

variable (F : Finset (Finset (Fin n))) (d : F → Fin n)

/-- The share of party `i` in the DNF scheme: for every set `C ∈ F` (one bit per set), the
secret is XOR-shared among the members of `C`: each member `j ≠ d C` gets the random bit
`r C j`, the designated member `d C` gets `s + ∑_{j ∈ C, j ≠ d C} r C j`, non-members get `0`. -/
def dnfShare (s : ZMod 2) (r : F → Fin n → ZMod 2) (i : Fin n) : F → ZMod 2 :=
  fun C => if i = d C then s + ∑ j ∈ (C : Finset (Fin n)).erase (d C), r C j
    else if i ∈ (C : Finset (Fin n)) then r C i else 0

/-- The DNF scheme: coins `r : F → Fin n → ZMod 2`, shares `F → ZMod 2` (|F| bits). -/
def dnfScheme : Scheme n (F → ZMod 2) where
  R := F → Fin n → ZMod 2
  share := dnfShare F d

/-- The XOR of the shares of the members of `C` is the secret. -/
theorem sum_dnfShare (s : ZMod 2) (r : F → Fin n → ZMod 2) (C : F) (hd : d C ∈ (C : Finset _)) :
    ∑ i ∈ (C : Finset (Fin n)), dnfShare F d s r i C = s := by
  rw [← Finset.add_sum_erase _ _ hd]
  have h2 : ∑ x ∈ (C : Finset (Fin n)).erase (d C), dnfShare F d s r x C =
      ∑ j ∈ (C : Finset (Fin n)).erase (d C), r C j := by
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.1 hx
    simp [dnfShare, hne, hmem]
  rw [h2]
  simp only [dnfShare]
  have key : ∀ a b : ZMod 2, a + b + b = a := by decide
  exact key _ _

/-- **Known result** (Ito–Saito–Nishizeki 1987; Benaloh–Leichter 1988), correctness part: if
every authorized set contains a member of `F` and `d C ∈ C`, the DNF scheme is perfectly
correct. -/
theorem correct_dnfScheme (A : Finset (Finset (Fin n)))
    (hgen : ∀ B ∈ A, ∃ C ∈ F, C ⊆ B) (hd : ∀ C : F, d C ∈ (C : Finset (Fin n))) :
    (dnfScheme F d).Correct A := by
  intro B hB s s' r r' h
  obtain ⟨C, hCF, hCB⟩ := hgen B hB
  let C' : F := ⟨C, hCF⟩
  rw [← sum_dnfShare F d s r C' (hd C'), ← sum_dnfShare F d s' r' C' (hd C')]
  exact Finset.sum_congr rfl fun i hi => congrFun (h i (hCB hi)) C'

/-- **Known result** (Ito–Saito–Nishizeki 1987; Benaloh–Leichter 1988), privacy part: if `A` is
up-closed and `F ⊆ A`, the DNF scheme is perfectly private. The proof is the classical one:
an unauthorized `T` misses some member `j C` of each `C ∈ F`, and flipping the coin `r C (j C)`
is a bijection of the coin space that maps secret-`0` views of `T` to secret-`1` views. -/
theorem private_dnfScheme (A : Finset (Finset (Fin n)))
    (hmono : ∀ B ∈ A, ∀ C : Finset (Fin n), B ⊆ C → C ∈ A) (hFA : F ⊆ A) :
    (dnfScheme F d).Private A := by
  intro T hT v
  have hj : ∀ C : F, ∃ j ∈ (C : Finset (Fin n)), j ∉ T := by
    intro C
    by_contra hcon
    push Not at hcon
    exact hT (hmono C.1 (hFA C.2) T hcon)
  choose j hjC hjT using hj
  let δ : F → Fin n → ZMod 2 := fun C => Pi.single (j C) 1
  have key : ∀ r : F → Fin n → ZMod 2, ∀ i ∈ T, dnfShare F d 0 r i = dnfShare F d 1 (r + δ) i := by
    intro r i hi
    funext C
    have hij : i ≠ j C := fun h => hjT C (h ▸ hi)
    unfold dnfShare
    by_cases hid : i = d C
    · simp only [hid, ↓reduceIte]
      have hjmem : j C ∈ (C : Finset (Fin n)).erase (d C) :=
        Finset.mem_erase.2 ⟨fun h => hij (hid.trans h.symm), hjC C⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, δ, Finset.sum_pi_single', hjmem, ite_true]
      have k2 : ∀ a : ZMod 2, 0 + a = 1 + (a + 1) := by decide
      exact k2 _
    · simp only [hid, ↓reduceIte]
      split_ifs
      · simp [δ, hij]
      · rfl
  show Nat.card {r : F → Fin n → ZMod 2 // ∀ i ∈ T, dnfShare F d 0 r i = v i} =
    Nat.card {r : F → Fin n → ZMod 2 // ∀ i ∈ T, dnfShare F d 1 r i = v i}
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.addRight δ) fun r =>
    forall₂_congr fun i hi => by rw [key r i hi]; rfl)

/-- **Known result** (Ito–Saito–Nishizeki 1987; Benaloh–Leichter 1988): for an access structure
`A` and any generating family `F ⊆ A` (every authorized set contains a member of `F`), the DNF
scheme is a perfect secret-sharing scheme for `A`. -/
theorem perfect_dnfScheme (A : Finset (Finset (Fin n))) (hA : IsAccessStructure A)
    (hFA : F ⊆ A) (hgen : ∀ B ∈ A, ∃ C ∈ F, C ⊆ B) (hd : ∀ C : F, d C ∈ (C : Finset (Fin n))) :
    (dnfScheme F d).Perfect A :=
  ⟨correct_dnfScheme F d A hgen hd, private_dnfScheme F d A hA.2 hFA⟩

end DNF

end Scheme

/-! ### Minimal authorized sets -/

/-- The minimal authorized sets of `A`. -/
def minimals {n : ℕ} (A : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  A.filter fun B => ∀ C ∈ A, C ⊆ B → C = B

theorem minimals_subset {n : ℕ} (A : Finset (Finset (Fin n))) : minimals A ⊆ A :=
  Finset.filter_subset _ _

/-- Every authorized set contains a minimal authorized set. -/
theorem exists_minimals_subset {n : ℕ} (A : Finset (Finset (Fin n))) :
    ∀ B ∈ A, ∃ C ∈ minimals A, C ⊆ B := by
  intro B hB
  have hne : (A.filter (· ⊆ B)).Nonempty := ⟨B, Finset.mem_filter.2 ⟨hB, subset_rfl⟩⟩
  obtain ⟨C, hC, hmin⟩ := (A.filter (· ⊆ B)).exists_min_image Finset.card hne
  obtain ⟨hCA, hCB⟩ := Finset.mem_filter.1 hC
  refine ⟨C, Finset.mem_filter.2 ⟨hCA, fun C' hC'A hC'C => ?_⟩, hCB⟩
  exact Finset.eq_of_subset_of_card_le hC'C
    (hmin C' (Finset.mem_filter.2 ⟨hC'A, hC'C.trans hCB⟩))

/-- The minimal authorized sets form an antichain, so by Sperner's theorem (Mathlib's
`IsAntichain.sperner`, used as stated) there are at most `choose n ⌊n/2⌋ ≤ 2 ^ n` of them. -/
theorem card_minimals_le {n : ℕ} (A : Finset (Finset (Fin n))) :
    (minimals A).card ≤ n.choose (n / 2) := by
  have h : IsAntichain (· ⊆ ·) (SetLike.coe (minimals A)) := by
    intro B hB C hC hBC hsub
    have hC' := (Finset.mem_filter.1 hC).2 B (Finset.mem_filter.1 hB).1 hsub
    exact hBC hC'
  simpa using h.sperner

/-- **Known result** (Ito–Saito–Nishizeki 1987, "Secret sharing scheme realizing general access
structure", Globecom '87; Benaloh–Leichter, CRYPTO '88; see Beimel's survey, IWCC 2011, §3.1):
every access structure on `n` parties admits a perfect one-bit secret-sharing scheme whose
shares are `ℓ`-bit strings, where `ℓ` is the number of minimal authorized sets; in particular
`ℓ ≤ choose n ⌊n/2⌋ ≤ 2 ^ n`. -/
theorem exists_perfect_scheme {n : ℕ} (A : Finset (Finset (Fin n))) (hA : IsAccessStructure A) :
    ∃ ℓ : ℕ, ℓ = (minimals A).card ∧ ℓ ≤ n.choose (n / 2) ∧ ℓ ≤ 2 ^ n ∧
      ∃ S : Scheme n (Fin ℓ → ZMod 2), S.Perfect A := by
  refine ⟨(minimals A).card, rfl, card_minimals_le A,
    (card_minimals_le A).trans (Nat.choose_le_two_pow _ _), ?_⟩
  have hd : ∀ C : minimals A, ∃ i, i ∈ (C : Finset (Fin n)) := by
    intro C
    by_contra hcon
    push Not at hcon
    have : (C : Finset (Fin n)) = ∅ := Finset.eq_empty_of_forall_notMem hcon
    exact hA.1 (this ▸ minimals_subset A C.2)
  choose d hd using hd
  have hP := Scheme.perfect_dnfScheme (minimals A) d A hA (minimals_subset A)
    (exists_minimals_subset A) hd
  let e : (minimals A → ZMod 2) ≃ (Fin (minimals A).card → ZMod 2) :=
    Equiv.arrowCongr ((Fintype.equivFin (minimals A)).trans
      (finCongr (Fintype.card_coe (minimals A)))) (Equiv.refl _)
  exact ⟨_, Scheme.perfect_mapShares e hP⟩

/-- **Open problem #13 (ProofAtlas list): polynomial-size perfect secret sharing.**
Paraphrase of the standard statement (Beimel, "Secret-sharing schemes: a survey", IWCC 2011,
open problem 1): *does every access structure on `n` parties admit a perfect secret-sharing
scheme (for a one-bit secret) whose share size is polynomial in `n`?* This is **open**: the best
known upper bounds are exponential (`2 ^ (0.637 n)`, Applebaum–Beimel–Nir–Peter 2020;
`1.5 ^ (n + o(n))`, Applebaum–Nir 2021; `exists_perfect_scheme` above gives the classical `choose n ⌊n/2⌋`), and
the best lower bound is `Ω(n² / log n)` (Csirmaz 1994).

Formalization: there are constants `c, k` such that for every `n` and every access structure `A`
on `Fin n` there is a perfect scheme whose shares are bit strings of length `ℓ ≤ c * n ^ k + c`.
Modelling simplifications: one-bit secret, uniform randomness on a finite nonempty set (see the
module docstring), all parties' shares of the same length (pad to the maximum share). -/
def PolySizeSecretSharing : Prop :=
  ∃ c k : ℕ, ∀ (n : ℕ) (A : Finset (Finset (Fin n))), IsAccessStructure A →
    ∃ ℓ : ℕ, ℓ ≤ c * n ^ k + c ∧ ∃ S : Scheme n (Fin ℓ → ZMod 2), S.Perfect A

/-! ### Polytopes: the polynomial Hirsch conjecture (statement only) -/

section Polytope

open Matrix

variable {d m : ℕ}

/-- The polyhedron `{x ∈ ℝ^d | a i ⬝ᵥ x ≤ b i for all i : Fin m}` (as a membership predicate). -/
def Feasible (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ i, a i ⬝ᵥ x ≤ b i

/-- The constraints tight at `x`. -/
def tight (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) : Set (Fin m) :=
  {i | a i ⬝ᵥ x = b i}

/-- `x` is a vertex of the polyhedron: feasible, and the normals of the tight constraints span
`ℝ^d` (equivalently, `x` is the unique solution of its tight equations). -/
def IsVertex (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ) (x : Fin d → ℝ) : Prop :=
  Feasible a b x ∧ Submodule.span ℝ (a '' tight a b x) = ⊤

/-- The graph (1-skeleton) of the polyhedron: vertices `u ≠ v` are adjacent when the constraints
tight at both have rank `d - 1`, i.e. the smallest face containing `u` and `v` is an edge
(its implicit-equality set is `tight u ∩ tight v`, and its dimension is `d` minus that rank). -/
def polyGraph (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ) :
    SimpleGraph {x : Fin d → ℝ // IsVertex a b x} :=
  SimpleGraph.fromRel fun u v =>
    Module.finrank ℝ (Submodule.span ℝ (a '' (tight a b u.1 ∩ tight a b v.1))) + 1 = d

/-- The polyhedron is bounded (a polytope). -/
def Bounded (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ M : ℝ, ∀ x, Feasible a b x → ∀ j, |x j| ≤ M

/-- **Open problem #12 (ProofAtlas list): polynomial diameter for polytopes (polynomial Hirsch
conjecture).** Paraphrase of the standard statement (Kalai; Santos, "A counterexample to the
Hirsch conjecture", Ann. of Math. 2012, §1): *is the diameter of the graph of every
`d`-dimensional polytope with `n` facets bounded by a polynomial in `n` (and `d`)?* This is
**open**; the original Hirsch bound `n - d` is false (Santos 2012), and the best known upper
bound is quasi-polynomial, `n ^ (log₂ d + 2)` (Kalai–Kleitman 1992; improved by Todd 2014 and
Sukegawa 2019).

Formalization: there are constants `c, k` such that for every bounded polyhedron
`{x | a i ⬝ᵥ x ≤ b i, i < m}` in `ℝ^d` and any two of its vertices, the (extended) graph distance
in its 1-skeleton is at most `c * m ^ k + c`. Modelling notes: polytopes are given by an
H-description with `m` inequalities (`m ≥` number of facets, with equality for irredundant
descriptions, so a bound polynomial in `m` for all descriptions is the same question); a bounded
nonempty polyhedron has `m ≥ d + 1` when `d ≥ 1`, so a polynomial in `m` alone also bounds `d`.
`SimpleGraph.edist` is `⊤` for disconnected vertices, so the statement also demands connectivity
(Balinski's theorem guarantees it for genuine polytopes). -/
def PolynomialHirsch : Prop :=
  ∃ c k : ℕ, ∀ (d m : ℕ) (a : Fin m → Fin d → ℝ) (b : Fin m → ℝ), Bounded a b →
    ∀ u v : {x : Fin d → ℝ // IsVertex a b x},
      (polyGraph a b).edist u v ≤ ((c * m ^ k + c : ℕ) : ℕ∞)

end Polytope

end CryptoLean.OpenProblems.SecretSharing

#print axioms CryptoLean.OpenProblems.SecretSharing.Scheme.perfect_dnfScheme
#print axioms CryptoLean.OpenProblems.SecretSharing.Scheme.correct_dnfScheme
#print axioms CryptoLean.OpenProblems.SecretSharing.Scheme.private_dnfScheme
#print axioms CryptoLean.OpenProblems.SecretSharing.card_minimals_le
#print axioms CryptoLean.OpenProblems.SecretSharing.exists_perfect_scheme
