import Mathlib

/-!
# Open problems on arithmetic statistics: class groups, Collatz, nonresidues, elliptic curves,
# and the Ramanujan tau function

ProofAtlas problems (releaseRank) 112, 170, 293, 312, 350, 415, 459, 481.

**All eight problems are OPEN.** Each appears below only as an unproved `def … : Prop` whose
docstring quotes the ProofAtlas `exactTarget` and lists every modelling choice.  Nothing in this
file proves, or claims progress towards, any of them.

Mathlib objects reused (no re-definitions):
* `QuadraticAlgebra ℚ d 0` (the field `ℚ(√d)` when `d` is not a square, via Mathlib's `Field`
  instance), `NumberField.RingOfIntegers` (`𝓞 K`), `ClassGroup`, `NumberField.classNumber`,
  `NumberField.discr`, `CommGroup.primaryComponent` (the Sylow `p`-subgroup of a finite abelian
  group), `MulAut`, `IsPGroup`;
* `CyclotomicField`, `NumberField.maximalRealSubfield`;
* `WeierstrassCurve`, `WeierstrassCurve.IsElliptic`, `WeierstrassCurve.j`,
  `WeierstrassCurve.minimal`, `WeierstrassCurve.HasGoodReduction`,
  `WeierstrassCurve.reduction` (reduction of a minimal model over a DVR, here `ℤ_[p] ⊂ ℚ_[p]`),
  `WeierstrassCurve.Affine.Point` (the group `E(𝔽_p)`, point at infinity included);
* `ModularForm.discriminant` (`Δ = η²⁴ = q ∏ (1 - qⁿ)²⁴`), `UpperHalfPlane.qExpansion`,
  `ModularForm.discriminant_qExpansion_coeff_one`;
* `ZMod`, `IsSquare`, `FiniteField.exists_nonsquare`.

## Modelling conventions shared by several problems

* **Quadratic fields.**  For a squarefree integer `d ≠ 1` the field `ℚ(√d)` is
  `QuadraticAlgebra ℚ d 0` (Mathlib's `Field` instance needs `Fact (¬ IsSquare (d : ℚ))`, which
  is supplied inside an existential, see `WithQuadField`).  Isomorphism classes of quadratic
  fields are in bijection with squarefree `d ≠ 0, 1` (standard), so "the set of quadratic fields
  with …" is modelled as "the set of squarefree `d` with …".
* **Elliptic curves over `ℚ` at a prime `p`.**  `E` is a `WeierstrassCurve ℚ` with `IsElliptic`.
  Its local data at `p` are read off a minimal model over `ℤ_[p]` (`localMinimal`): good
  reduction is Mathlib's `HasGoodReduction ℤ_[p]`, and `#E(𝔽_p)` is `Nat.card` of the points
  (with `O`) of the reduced curve over the residue field of `ℤ_[p]` (which is `𝔽_p`).  A
  minimal model over `ℤ_[p]` has good reduction iff a global minimal model over `ℤ` has
  `p ∤ Δ_min`, so this is the usual notion.
* **CM.**  Mathlib has no endomorphism ring of an elliptic curve.  "`E/ℚ` has complex
  multiplication" is modelled by the known classification (Deuring / class number one; see
  Silverman, *Advanced Topics*, Appendix A.3): `E/ℚ` has CM over `ℚ̄` iff `j(E)` is one of the
  13 rational CM `j`-invariants `cmJInvariants`.  This substitution is a modelling choice
  justified by a known theorem that is *not* formalised here.
* **Supersingular reduction** (problem 459).  Mathlib has no `p`-torsion of `E` over `𝔽̄_p`.
  For a prime `p` of good reduction, `E` is supersingular at `p` iff `p ∣ a_p` where
  `a_p = p + 1 - #E(𝔽_p)` (Silverman, *AEC*, Exercise 5.10; for `p ≥ 5` this is `a_p = 0` by
  Hasse).  We use the divisibility criterion as the definition (`IsSupersingularAt`).

## What is missing from Mathlib (gap notes)

* **Galois images of elliptic curves** (problem 415).  Zywina's corrected Koblitz constant is
  `C_E = lim_m δ_E(m) / ∏_{ℓ ∣ m} (1 - 1/ℓ)` (limit over `m` ordered by divisibility) with
  `δ_E(m) = #{A ∈ G(m) : det(I - A) ∈ (ℤ/m)ˣ} / #G(m)`, `G(m)` the image of the mod-`m` Galois
  representation.  Mathlib has no mod-`m` Galois representation of `E`.  By the Chebotarev
  density theorem (also not in Mathlib), `δ_E(m)` equals the natural density of the primes of
  good reduction with `gcd(#E(𝔽_p), m) = 1`, because `#E(𝔽_p) ≡ det(I - ρ_m(Frob_p)) (mod m)`.
  The statement below therefore *characterises* `δ_E(m)` by that density and takes the limit
  along the cofinal divisibility chain `m = k!`.  The existence of these densities (Chebotarev)
  and of the limit (Zywina) are known theorems that are hypotheses of the Prop, not proved here.
* **Endomorphism rings / CM** and **supersingularity** of elliptic curves: see the conventions
  above.
* **Hall's identity** `∑_B |B|^{-u} / |Aut B| = ∏_{i ≥ 1+u} (1 - p^{-i})⁻¹` (problem 112) is not
  in Mathlib; the quoted target itself gives the product form of `Z_u(p)`, which we use.
* **Ramanujan's `τ` as an integer sequence** (problem 481).  Mathlib has `Δ` and its
  `q`-expansion, with `τ(1) = 1` proved, but no computation of further coefficients; the
  identification of `qExpansion 1 Δ` with the formal product `X ∏ (1 - Xᵏ)²⁴` beyond the
  linear term is not in Mathlib.  So no finite check of `τ(n) ≠ 0` for `n ≥ 2` is made here.

## Known results proved here (all reuse Mathlib)

* `exists_nonresidue`, `leastNonresidue_spec`, `leastNonresidue_lt_sqrt_add_one`: for an odd
  prime `p` the least positive quadratic nonresidue exists and is `< √p + 1` (classical,
  elementary; Vinogradov 1918 era folklore — e.g. Nathanson, *Elementary Methods in Number
  Theory*, or Ireland–Rosen, Ch. 5 exercises).
* `collatz_reaches_one_le_1000`: **finite check** — every `1 ≤ n ≤ 1000` reaches `1` under the
  Collatz map.  This is a finite verification, *not* partial progress on problem 170.
* `tau_one_ne_zero`: **finite check** — `τ(1) = 1 ≠ 0` (Mathlib's
  `discriminant_qExpansion_coeff_one`), the case `n = 1` of problem 481 only.
-/

namespace CryptoLean.OpenProblems.NumberTheory.ArithmeticStats

open NumberField Filter Topology

/-! ## Quadratic fields -/

/-- `ℚ(√d)` as Mathlib's `QuadraticAlgebra ℚ d 0`; a field once `¬ IsSquare (d : ℚ)`. -/
abbrev QuadField (d : ℤ) : Type := QuadraticAlgebra ℚ (d : ℚ) 0

/-- `WithQuadField d P` says that `d` is not a square in `ℚ` and the number field
`K = ℚ(√d)` (with Mathlib's field and number-field structures) satisfies `P K`.
For squarefree `d ≠ 1` the first clause holds automatically. -/
def WithQuadField (d : ℤ) (P : ∀ (K : Type) [Field K] [NumberField K], Prop) : Prop :=
  ∃ h : ¬ IsSquare (d : ℚ),
    haveI : Fact (¬ IsSquare (d : ℚ)) := ⟨h⟩
    haveI : NumberField (QuadField d) := {}
    P (QuadField d)

/-! ## Problem 112: Cohen–Lenstra heuristics for quadratic fields -/

/-- The squarefree `d ≠ 1` with `ℚ(√d)` imaginary (`u = 0`, `d < 0`) or real (`u = 1`, `d > 1`)
and `|disc ℚ(√d)| < X` whose field also satisfies `P`. -/
def quadFamily (u : ℕ) (X : ℕ) (P : ∀ (K : Type) [Field K] [NumberField K], Prop) : Set ℤ :=
  {d | Squarefree d ∧ d ≠ 1 ∧ (if u = 0 then d < 0 else 1 < d) ∧
    WithQuadField d (fun K _ _ => |NumberField.discr K| < X ∧ P K)}

/-- **Problem 112 (OPEN): Cohen–Lenstra heuristics for quadratic fields.**

ProofAtlas exactTarget (quoted): "For u in {0,1} let K_u(X) be the set of isomorphism classes of
quadratic number fields K with |disc(K)| < X that are imaginary (u = 0) or real (u = 1). For each
fixed odd prime p and each finite abelian p-group A, prove that the limit as X tends to infinity
of #{K in K_u(X) : Cl(K)[p^infinity] is isomorphic to A} / #K_u(X) exists and equals
(1/Z_u(p)) * |A|^{-u} / |Aut(A)|, where Z_u(p) is the sum over isomorphism classes of finite
abelian p-groups B of |B|^{-u}/|Aut(B)| (so Z_0(p) = prod_{i>=1}(1-p^{-i})^{-1} and
Z_1(p) = prod_{i>=2}(1-p^{-i})^{-1}). Cl(K) is the ordinary ideal class group and
Cl(K)[p^infinity] its Sylow p-subgroup. No assertion is made for p = 2, for narrow class groups,
for a joint law over several primes, or for any non-quadratic family."

Modelling choices:
* isomorphism classes of quadratic fields ↔ squarefree `d ≠ 0, 1` (`d < 0` imaginary,
  `d > 1` real), `K = QuadraticAlgebra ℚ d 0`; `|disc K|` is Mathlib's `NumberField.discr`;
* `X → ∞` along the natural numbers (the counts are step functions of `X`, so this is
  equivalent to real `X`);
* `Cl(K) = ClassGroup (𝓞 K)` and `Cl(K)[p^∞] = CommGroup.primaryComponent (ClassGroup (𝓞 K)) p`;
* "finite abelian `p`-group `A`": a type with `CommGroup`, `Finite`, `IsPGroup p A`; `|Aut A|`
  is `Nat.card (MulAut A)`;
* `1/Z_u(p)` is written as the product `∏_{i ≥ 0} (1 - p^{-(i+1+u)})` given in the quote
  (Hall's identity relating it to the sum over `B` is a known result not in Mathlib);
* the ratio is a real number (`0/0 = 0` convention is irrelevant: `#K_u(X) > 0` for large `X`). -/
def CohenLenstraQuadratic : Prop :=
  ∀ u : ℕ, u ≤ 1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup p A →
      Tendsto
        (fun X : ℕ =>
          ((quadFamily u X (fun K _ _ =>
              Nonempty (CommGroup.primaryComponent (ClassGroup (𝓞 K)) p ≃* A))).ncard : ℝ) /
            ((quadFamily u X (fun _ _ _ => True)).ncard : ℝ))
        atTop
        (𝓝 ((∏' i : ℕ, (1 - ((p : ℝ)⁻¹) ^ (i + 1 + u))) *
              ((Nat.card A : ℝ)⁻¹) ^ u / (Nat.card (MulAut A) : ℝ)))

/-! ## Problem 350: Gauss's real quadratic class number one conjecture -/

/-- **Problem 350 (OPEN): Gauss's conjecture that infinitely many real quadratic fields have
class number one.**

ProofAtlas exactTarget (quoted): "Resolve whether infinitely many squarefree integers d>1 have
ordinary ideal class number h(Q(sqrt(d)))=|Cl(O_d)|=1, where O_d is the full ring of integers:
Z[(1+sqrt(d))/2] for d=1 mod 4 and Z[sqrt(d)] for d=2 or 3 mod 4, and Cl(O_d) is the group of
nonzero fractional ideals modulo all nonzero principal fractional ideals."

The Prop is the affirmative answer (Gauss's expectation); the open problem is to decide it.
Modelling choices: `ℚ(√d) = QuadraticAlgebra ℚ d 0`; `O_d` is Mathlib's ring of integers
`𝓞 ℚ(√d)` (that it equals the quoted explicit order is the standard description, not
reproved); `h = NumberField.classNumber`, the cardinality of `ClassGroup (𝓞 K)`, which is
fractional ideals modulo principal ones. -/
def GaussRealQuadraticClassNumberOne : Prop :=
  Set.Infinite {d : ℕ | 1 < d ∧ Squarefree d ∧
    WithQuadField (d : ℤ) (fun K _ _ => NumberField.classNumber K = 1)}

/-! ## Problem 312: the Kummer–Vandiver conjecture -/

/-- **Problem 312 (OPEN): the Kummer–Vandiver conjecture.**

ProofAtlas exactTarget (quoted): "Prove that the prime p does not divide the class number
h+(Q(zeta_p)) of the maximal real subfield of the p-th cyclotomic field for all primes p."

Modelling choices: `ℚ(ζ_p) = CyclotomicField p ℚ`; its maximal real subfield is Mathlib's
`NumberField.maximalRealSubfield` (the largest totally real subfield, which for `p` odd is
`ℚ(ζ_p + ζ_p⁻¹)`, and for `p = 2` is `ℚ` itself); `h⁺` is `NumberField.classNumber`. -/
def KummerVandiver : Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    haveI : Fact p.Prime := ⟨hp⟩
    ¬ p ∣ NumberField.classNumber (maximalRealSubfield (CyclotomicField p ℚ))

/-! ## Problem 170: the Collatz conjecture -/

/-- The Collatz map `N ↦ N/2` (`N` even), `N ↦ 3N+1` (`N` odd). -/
def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- **Problem 170 (OPEN): the Collatz conjecture.**

ProofAtlas exactTarget (quoted): "Prove or disprove that, for every positive integer N, repeated
application of N -> N/2 when N is even and N -> 3N+1 when N is odd eventually reaches 1."

The Prop is the "prove" alternative; the open problem is to decide it.  No modelling
simplification: "eventually reaches 1" is "some iterate equals 1". -/
def CollatzConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ k : ℕ, collatzStep^[k] n = 1

/-- Bounded Collatz test: does `n` reach `1` within `fuel` steps? -/
def reachesOneWithin : ℕ → ℕ → Bool
  | 0, n => n == 1
  | fuel + 1, n => n == 1 || reachesOneWithin fuel (collatzStep n)

theorem reachesOneWithin_sound : ∀ (fuel n : ℕ), reachesOneWithin fuel n = true →
    ∃ k : ℕ, collatzStep^[k] n = 1
  | 0, n, h => ⟨0, by simpa [reachesOneWithin] using h⟩
  | fuel + 1, n, h => by
    simp only [reachesOneWithin, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨k, hk⟩ := reachesOneWithin_sound fuel _ h
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **Finite check (not progress on the conjecture):** every `n` with `1 ≤ n ≤ 1000` reaches `1`
under the Collatz map (the longest trajectory in this range, `n = 871`, takes 178 steps).
Verified by kernel evaluation of `reachesOneWithin 200`. -/
theorem collatz_reaches_one_le_1000 (n : ℕ) (h0 : 0 < n) (h1 : n ≤ 1000) :
    ∃ k : ℕ, collatzStep^[k] n = 1 := by
  have hall : (List.range 1001).all (fun n => n == 0 || reachesOneWithin 200 n) = true := by
    set_option maxRecDepth 100000 in decide
  rw [List.all_eq_true] at hall
  have := hall n (List.mem_range.2 (by omega))
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h | h
  · omega
  · exact reachesOneWithin_sound _ _ h

/-! ## Problem 293: Vinogradov's conjecture on the least quadratic nonresidue -/

/-- The least positive quadratic nonresidue `n_p` modulo `p` (junk value `0` if none exists,
e.g. `p = 2`). -/
noncomputable def leastNonresidue (p : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ¬ IsSquare (n : ZMod p)}

/-- **Problem 293 (OPEN): Vinogradov's conjecture on the least quadratic nonresidue.**

ProofAtlas exactTarget (quoted): "Let n_p denote the least quadratic non-residue modulo an odd
prime p. Prove unconditionally that for every eps > 0 one has n_p <<_eps p^eps."

Modelling choices: `n_p = leastNonresidue p` (least positive `n` that is not a square in
`ZMod p`); `n_p ≪_ε p^ε` is spelled out as "there is a constant `C` (depending on `ε` only)
with `n_p ≤ C · p^ε` for every odd prime `p`". -/
def VinogradovLeastNonresidue : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    (leastNonresidue p : ℝ) ≤ C * (p : ℝ) ^ ε

/-- **Known result**: modulo an odd prime there is a positive quadratic nonresidue
(half of `(ℤ/p)ˣ` are nonsquares; Mathlib's `FiniteField.exists_nonsquare`). -/
theorem exists_nonresidue (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ n : ℕ, 0 < n ∧ n < p ∧ ¬ IsSquare (n : ZMod p) := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  refine ⟨a.val, ?_, ZMod.val_lt a, by rwa [ZMod.natCast_zmod_val]⟩
  rcases Nat.eq_zero_or_pos a.val with h | h
  · exact absurd (by rw [(ZMod.val_eq_zero a).1 h]; exact IsSquare.zero) ha
  · exact h

/-- **Known result**: `n_p` is a positive nonresidue, `n_p < p`, and every `0 < k < n_p` is a
quadratic residue mod `p` (`p` an odd prime). -/
theorem leastNonresidue_spec (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    0 < leastNonresidue p ∧ leastNonresidue p < p ∧ ¬ IsSquare (leastNonresidue p : ZMod p) ∧
      ∀ k : ℕ, 0 < k → k < leastNonresidue p → IsSquare (k : ZMod p) := by
  obtain ⟨a, ha0, hap, ha⟩ := exists_nonresidue p hp2
  have hne : ({n : ℕ | 0 < n ∧ ¬ IsSquare (n : ZMod p)} : Set ℕ).Nonempty := ⟨a, ha0, ha⟩
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, lt_of_le_of_lt (Nat.sInf_le ⟨ha0, ha⟩) hap, hmem.2, fun k hk hkn => ?_⟩
  by_contra hks
  exact absurd (Nat.sInf_le (⟨hk, hks⟩ : k ∈ {n : ℕ | 0 < n ∧ ¬ IsSquare (n : ZMod p)}))
    (not_le.2 hkn)

/-- **Known result** (classical elementary bound; e.g. Ireland–Rosen, *A Classical Introduction
to Modern Number Theory*, Ch. 5; Nathanson, *Elementary Methods in Number Theory*, §2):
for every odd prime `p`, the least quadratic nonresidue satisfies `n_p < √p + 1`.

Proof: with `n = n_p` and `m = ⌊p/n⌋ + 1`, `0 < mn - p < n`, so `mn ≡ mn - p` is a residue,
forcing `m` to be a nonresidue, so `m ≥ n`, whence `n(n-1) < p`. -/
theorem leastNonresidue_lt_sqrt_add_one (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (leastNonresidue p : ℝ) < Real.sqrt p + 1 := by
  obtain ⟨hn0, hnp, hn, hmin⟩ := leastNonresidue_spec p hp2
  set n := leastNonresidue p with hndef
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  have hn1 : n ≠ 1 := by rintro h; rw [h] at hn; exact hn (by simp)
  have hn2 : 2 ≤ n := by omega
  -- `n` does not divide `p`
  have hmod : p % n ≠ 0 := by
    intro h
    have hdvd : n ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp.out).1 hdvd with h' | h' <;> omega
  obtain ⟨q, hq⟩ : ∃ q, q = p / n := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = p % n := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = q + 1 := ⟨_, rfl⟩
  have hdiv : n * q + s = p := by rw [hq, hs]; exact Nat.div_add_mod p n
  have hmodlt : s < n := by rw [hs]; exact Nat.mod_lt p hn0
  rw [← hs] at hmod
  -- r = m n - p
  obtain ⟨r, hr⟩ : ∃ r, r = n - s := ⟨_, rfl⟩
  have hr0 : 0 < r := by omega
  have hrn : r < n := by omega
  have hmn : m * n = r + p := by
    subst hm hr; rw [← hdiv, add_mul, one_mul, mul_comm q n]; omega
  have hrsq : IsSquare ((m : ZMod p) * n) := by
    have : ((m : ZMod p) * n) = (r : ZMod p) := by
      rw [← Nat.cast_mul, hmn, Nat.cast_add, ZMod.natCast_self, add_zero]
    rw [this]; exact hmin r hr0 hrn
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hmpos : 0 < m := by omega
    have := Nat.le_of_dvd hmpos hdvd
    have : q ≤ p / 2 := hq ▸ Nat.div_le_div_left hn2 (by norm_num)
    have : p / 2 < p - 1 := by omega
    omega
  have hmnr : ¬ IsSquare (m : ZMod p) := by
    intro hmsq
    apply hn
    have : (n : ZMod p) = ((m : ZMod p) * n) / m := by field_simp
    rw [this]; exact hrsq.div hmsq
  have hmge : n ≤ m := by
    by_contra h
    exact hmnr (hmin m (by omega) (by omega))
  -- n (n - 1) ≤ n (p / n) ≤ p, with strict inequality since n ∤ p
  have hle : n * (n - 1) ≤ p := by
    have : n - 1 ≤ q := by omega
    calc n * (n - 1) ≤ n * q := Nat.mul_le_mul_left _ this
      _ ≤ p := by omega
  have hlt : n * (n - 1) < p := by
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso; apply hmod; rw [hs, ← h]; simp
  have hreal : ((n : ℝ) - 1) ^ 2 < p := by
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    have h2 : ((n * (n - 1) : ℕ) : ℝ) < p := by exact_mod_cast hlt
    push_cast [Nat.cast_mul] at h2
    rw [h1] at h2
    nlinarith
  have hpos : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    linarith
  have := Real.lt_sqrt hpos |>.2 hreal
  linarith

/-! ## Elliptic curves over `ℚ`: local data at a prime -/

/-- A minimal model of `E/ℚ` over `ℤ_[p] ⊂ ℚ_[p]`. -/
noncomputable abbrev localMinimal (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve ℚ_[p] :=
  (E.baseChange ℚ_[p]).minimal ℤ_[p]

/-- `E` has good reduction at `p`. -/
def HasGoodReductionAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  (localMinimal E p).HasGoodReduction ℤ_[p]

/-- `#Ẽ(𝔽_p)`: the number of points (including `O`) of the reduction of a minimal model at `p`. -/
noncomputable def reducedPointCount (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Nat.card ((localMinimal E p).reduction ℤ_[p]).toAffine.Point

/-- `E` is supersingular at the good prime `p`: `p ∣ a_p = p + 1 - #E(𝔽_p)` (see the module
doc for why this criterion is used as the definition). -/
def IsSupersingularAt (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  HasGoodReductionAt E p ∧ (p : ℤ) ∣ (p : ℤ) + 1 - reducedPointCount E p

/-- The 13 `j`-invariants of elliptic curves over `ℚ` with complex multiplication. -/
def cmJInvariants : Set ℚ :=
  {0, 1728, -3375, 8000, -32768, 54000, 287496, -884736, -12288000, 16581375, -884736000,
    -147197952000, -262537412640768000}

/-- The number of primes `p` with `p ≤ x` (or `p < x` if `strict`) satisfying `P`. -/
noncomputable def primeCount (x : ℝ) (strict : Bool) (P : ∀ (p : ℕ) [Fact p.Prime], Prop) : ℕ :=
  Set.ncard {p : ℕ | (if strict then (p : ℝ) < x else (p : ℝ) ≤ x) ∧
    ∃ hp : p.Prime, haveI : Fact p.Prime := ⟨hp⟩; P p}

/-! ## Problem 459: the Lang–Trotter conjecture for supersingular primes -/

/-- **Problem 459 (OPEN): the Lang–Trotter conjecture for supersingular primes.**

ProofAtlas exactTarget (quoted): "For every elliptic curve E over Q without complex
multiplication, prove or refute the Lang-Trotter asymptotic that the number of primes p < X at
which E has supersingular reduction is asymptotic to C_E sqrt(X)/log X for a positive constant
C_E depending on E."

The Prop is the "prove" alternative.  Modelling choices: `E` is an elliptic `WeierstrassCurve ℚ`;
"without CM" is `j(E) ∉ cmJInvariants`; supersingular reduction is `IsSupersingularAt`; the
count is over primes `p < X` (real `X → ∞`); `f ~ g` is `f/g → 1`. -/
def LangTrotterSupersingular : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun X : ℝ => (primeCount X true (fun p _ => IsSupersingularAt E p) : ℝ) /
          (C * Real.sqrt X / Real.log X)) atTop (𝓝 1)

/-! ## Problem 415: Koblitz's conjecture (Zywina's corrected form) -/

/-- `δ` is the natural density, among all primes, of the primes `p` of good reduction for `E`
with `gcd(#E(𝔽_p), m) = 1`. -/
def IsCoprimeOrderDensity (E : WeierstrassCurve ℚ) (m : ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (primeCount x false (fun p _ => HasGoodReductionAt E p ∧
          Nat.Coprime (reducedPointCount E p) m) : ℝ) /
        (primeCount x false (fun _ _ => True) : ℝ)) atTop (𝓝 δ)

/-- `C` is Zywina's corrected Koblitz constant of `E`, given the densities `δ m` of
`IsCoprimeOrderDensity`: `C = lim δ(m) / ∏_{ℓ ∣ m} (1 - 1/ℓ)` along `m = k!`. -/
def IsKoblitzConstant (E : WeierstrassCurve ℚ) (C : ℝ) : Prop :=
  ∃ δ : ℕ → ℝ, (∀ m, 0 < m → IsCoprimeOrderDensity E m (δ m)) ∧
    Tendsto (fun k : ℕ => δ k.factorial /
        ∏ ℓ ∈ k.factorial.primeFactors, (1 - (ℓ : ℝ)⁻¹)) atTop (𝓝 C)

/-- **Problem 415 (OPEN): Koblitz's conjecture on prime orders of reductions (Zywina's
corrected constant).**

ProofAtlas exactTarget (quoted): "For every non-CM elliptic curve E over Q with corrected
Koblitz constant C_E>0, prove that #{p≤x: p is of good reduction and #E(F_p) is prime} is
asymptotic to C_E x/(log x)^2."

Modelling choices: `E` is an elliptic `WeierstrassCurve ℚ`; non-CM is `j(E) ∉ cmJInvariants`;
good reduction and `#E(𝔽_p)` are read off a minimal model over `ℤ_[p]`; the corrected constant
`C_E` is characterised by `IsKoblitzConstant` (Zywina's limit, with `δ_E(m)` characterised by the
Chebotarev density of good primes with `gcd(#E(𝔽_p), m) = 1` — see the gap note: Mathlib has no
Galois representations of `E`, and Chebotarev is not in Mathlib); the limit over `m` ordered by
divisibility is taken along the cofinal chain `m = k!`; `f ~ g` is `f/g → 1` as real `x → ∞`. -/
def KoblitzConjecture : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], E.j ∉ cmJInvariants →
    ∀ C : ℝ, IsKoblitzConstant E C → 0 < C →
      Tendsto (fun x : ℝ =>
          (primeCount x false (fun p _ => HasGoodReductionAt E p ∧
              (reducedPointCount E p).Prime) : ℝ) /
            (C * x / Real.log x ^ 2)) atTop (𝓝 1)

/-! ## Problem 481: Lehmer's conjecture on the nonvanishing of `τ(n)` -/

/-- Ramanujan's `τ(n)`: the `n`-th coefficient of the `q`-expansion (at width `1`) of Mathlib's
modular discriminant `Δ = η²⁴ = q ∏_{k ≥ 1} (1 - qᵏ)²⁴`. -/
noncomputable def ramanujanTau (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff n

/-- **Problem 481 (OPEN): Lehmer's conjecture.**

ProofAtlas exactTarget (quoted): "Prove that Ramanujan's tau function never vanishes:
tau(n) != 0 for every positive integer n, where tau(n) are the Fourier coefficients of the
weight-12 cusp form Delta(z) = q prod_{k>=1} (1-q^k)^24."

Modelling choices: `τ(n)` is the coefficient of `qⁿ` in Mathlib's `UpperHalfPlane.qExpansion 1`
of `ModularForm.discriminant` (complex-valued; integrality is not used).  No other
simplification. -/
def LehmerTauNonvanishing : Prop :=
  ∀ n : ℕ, 0 < n → ramanujanTau n ≠ 0

/-- **Finite check** (`n = 1` only, not progress on the conjecture): `τ(1) = 1 ≠ 0`.
Known result: the leading coefficient of `Δ = q - 24q² + ⋯`
(Mathlib's `ModularForm.discriminant_qExpansion_coeff_one`). -/
theorem tau_one_ne_zero : ramanujanTau 1 ≠ 0 := by
  simp [ramanujanTau, ModularForm.discriminant_qExpansion_coeff_one]

end CryptoLean.OpenProblems.NumberTheory.ArithmeticStats

#print axioms CryptoLean.OpenProblems.NumberTheory.ArithmeticStats.collatz_reaches_one_le_1000
#print axioms CryptoLean.OpenProblems.NumberTheory.ArithmeticStats.exists_nonresidue
#print axioms CryptoLean.OpenProblems.NumberTheory.ArithmeticStats.leastNonresidue_spec
#print axioms CryptoLean.OpenProblems.NumberTheory.ArithmeticStats.leastNonresidue_lt_sqrt_add_one
#print axioms CryptoLean.OpenProblems.NumberTheory.ArithmeticStats.tau_one_ne_zero
