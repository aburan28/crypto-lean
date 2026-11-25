import Mathlib

/-!
# Finite projective planes: open problems #24 and #27

We reuse Mathlib's `Configuration.ProjectivePlane P L` (points `P`, lines `L`, incidence
`p ∈ l`), its `order`, and the counting theorems `card_points`, `card_lines`,
`pointCount_eq`, `lineCount_eq`. The Desarguesian plane `PG(2, K)` is Mathlib's instance
`Configuration.ofField` on `ℙ K (Fin 3 → K)` (points and lines both projective points,
incidence = orthogonality).

* Open problem #24 (non-prime-power orders) and its order-12 case are stated only as
  `Prop` definitions (`NonPrimePowerPlaneExists`, `PlaneOfOrderTwelveExists`); they are
  **not** proved here and remain open.
* Open problem #27 (planes of prime order are Desarguesian) is stated as the `Prop`
  `PrimeOrderPlanesUnique`; it is **not** proved and remains open.
* Proved (known results): the Fano plane is a projective plane of order 2; `PG(2, K)` has
  order `|K|` for every finite field `K`, hence a projective plane of every prime-power order
  exists; counting consequences for a hypothetical plane of order 12.
-/

namespace CryptoLean.OpenProblems.ProjectivePlanes

open Configuration
open scoped LinearAlgebra.Projectivization

/-! ## Isomorphism of incidence structures -/

/-- Two incidence structures `(P, L, ∈)` and `(P', L', ∈)` are isomorphic if there are
bijections of points and of lines that preserve and reflect incidence. -/
def IncidenceIso (P L P' L' : Type*) [Membership P L] [Membership P' L'] : Prop :=
  ∃ (e : P ≃ P') (f : L ≃ L'), ∀ (p : P) (l : L), p ∈ l ↔ e p ∈ f l

/-! ## Open problem statements (unproved) -/

/-- **Open problem #24 (ProofAtlas rank 355): finite projective planes of non-prime-power
order.** Statement (standard formulation; ProofAtlas text not available offline): "Does there exist a finite projective plane whose order is not a
prime power?" (Prime power conjecture: every finite projective plane has prime-power order.)

Modelling: a finite projective plane is Mathlib's `Configuration.ProjectivePlane P L` with
`P`, `L` finite types in `Type`; its order is `Configuration.ProjectivePlane.order`.
The existence question is recorded as this `Prop`; it is OPEN and not proved here. -/
def NonPrimePowerPlaneExists : Prop :=
  ∃ (P L : Type) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P) (_ : Finite L),
    ¬ IsPrimePow (ProjectivePlane.order P L)

/-- The smallest undecided case of open problem #24: does a projective plane of order 12
exist? (Order 6 is excluded by Bruck–Ryser, order 10 by Lam–Thiel–Swiercz 1989; order 12
is open.) Stated only as a `Prop`; OPEN and not proved here. -/
def PlaneOfOrderTwelveExists : Prop :=
  ∃ (P L : Type) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P) (_ : Finite L),
    ProjectivePlane.order P L = 12

/-- **Open problem #27 (ProofAtlas rank 476): uniqueness of projective planes of prime
order.** Statement (standard formulation; ProofAtlas text not available offline): "Is every finite projective plane of prime order `p`
Desarguesian, i.e. isomorphic to `PG(2, p)`?"

Modelling: `PG(2, p)` is Mathlib's plane on `ℙ (ZMod p) (Fin 3 → ZMod p)`; isomorphism is
`IncidenceIso` (a pair of bijections preserving incidence both ways). Planes are taken in
`Type`. Known for `p = 2, 3, 5, 7`; OPEN in general and not proved here. -/
def PrimeOrderPlanesUnique : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P L : Type) [Membership P L] [ProjectivePlane P L]
    [Finite P] [Finite L], ProjectivePlane.order P L = p →
    IncidenceIso P L (ℙ (ZMod p) (Fin 3 → ZMod p)) (ℙ (ZMod p) (Fin 3 → ZMod p))

/-! ## The Fano plane -/

/-- Lines of the Fano plane, indexed by `Fin 7`. -/
structure FanoLine where
  idx : Fin 7
  deriving DecidableEq

instance : Fintype FanoLine :=
  Fintype.ofEquiv (Fin 7) ⟨FanoLine.mk, FanoLine.idx, fun _ => rfl, fun _ => rfl⟩

/-- Cyclic Fano plane from the perfect difference set `{0, 1, 3} ⊂ ℤ/7`: point `p` lies on
line `l` iff `p - l ∈ {0, 1, 3}` (mod 7). -/
instance : Membership (Fin 7) FanoLine :=
  ⟨fun l p => p - l.idx ∈ ({0, 1, 3} : Finset (Fin 7))⟩

instance (p : Fin 7) (l : FanoLine) : Decidable (p ∈ l) :=
  inferInstanceAs (Decidable (p - l.idx ∈ ({0, 1, 3} : Finset (Fin 7))))

theorem fano_line_exists : ∀ p q : Fin 7, p ≠ q → ∃ l : FanoLine, p ∈ l ∧ q ∈ l := by
  decide

theorem fano_point_exists : ∀ l m : FanoLine, l ≠ m → ∃ p : Fin 7, p ∈ l ∧ p ∈ m := by
  decide

theorem fano_eq_or_eq : ∀ (p₁ p₂ : Fin 7) (l₁ l₂ : FanoLine),
    p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂ := by
  decide

/-- **Known result** (Fano 1892; see Hughes–Piper, *Projective Planes*, Ch. 3): the cyclic
Fano configuration on 7 points and 7 lines is a projective plane. -/
noncomputable instance fanoPlane : ProjectivePlane (Fin 7) FanoLine where
  exists_point := by decide
  exists_line := by decide
  eq_or_eq := fun h₁ h₂ h₃ h₄ => fano_eq_or_eq _ _ _ _ h₁ h₂ h₃ h₄
  mkPoint := fun h => Classical.choose (fano_point_exists _ _ h)
  mkPoint_ax := fun h => Classical.choose_spec (fano_point_exists _ _ h)
  mkLine := fun h => Classical.choose (fano_line_exists _ _ h)
  mkLine_ax := fun h => Classical.choose_spec (fano_line_exists _ _ h)
  exists_config := ⟨5, 1, 0, ⟨2⟩, ⟨0⟩, ⟨1⟩, by decide⟩

/-- **Known result** (Hughes–Piper, *Projective Planes*, Ch. 3): the Fano plane has order 2,
i.e. 3 points per line and 3 lines per point. -/
theorem fano_order : ProjectivePlane.order (Fin 7) FanoLine = 2 := by
  have h := ProjectivePlane.card_points (Fin 7) FanoLine
  rw [Fintype.card_fin] at h
  set n := ProjectivePlane.order (Fin 7) FanoLine
  have hn : n ≤ 2 := by nlinarith
  interval_cases n <;> omega

/-- **Known result**: a projective plane of order 2 exists (the Fano plane). -/
theorem exists_plane_of_order_two :
    ∃ (P L : Type) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P)
      (_ : Finite L), ProjectivePlane.order P L = 2 :=
  ⟨Fin 7, FanoLine, inferInstance, fanoPlane, inferInstance, inferInstance, fano_order⟩

/-! ## Desarguesian planes `PG(2, q)` -/

/-- **Known result** (Veblen–Bussey 1906; Hughes–Piper, *Projective Planes*, Ch. 1): for a
finite field `K`, the plane `PG(2, K)` has order `|K|`. -/
theorem order_pg2 (K : Type) [Field K] [Fintype K] [DecidableEq K] :
    ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) = Fintype.card K := by
  classical
  let _ : Fintype (ℙ K (Fin 3 → K)) := Fintype.ofFinite _
  have h := ProjectivePlane.card_points (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  have hc := Projectivization.card_of_finrank K (Fin 3 → K) (n := 3) (by simp)
  rw [← Nat.card_eq_fintype_card, hc, Nat.card_eq_fintype_card] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one] at h
  set n := ProjectivePlane.order (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K))
  set q := Fintype.card K
  rcases lt_trichotomy n q with hlt | heq | hgt
  · nlinarith
  · exact heq
  · nlinarith

/-- **Known result** (Veblen–Bussey 1906; Hughes–Piper, Ch. 1): for every prime power `q`
there is a finite projective plane of order `q`, namely `PG(2, 𝔽_q)`. -/
theorem exists_plane_of_prime_power_order {q : ℕ} (hq : IsPrimePow q) :
    ∃ (P L : Type) (_ : Membership P L) (_ : ProjectivePlane P L) (_ : Finite P)
      (_ : Finite L), ProjectivePlane.order P L = q := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have : Fact p.Prime := ⟨hp.nat_prime⟩
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  refine ⟨ℙ (GaloisField p k) (Fin 3 → GaloisField p k),
    ℙ (GaloisField p k) (Fin 3 → GaloisField p k), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  rw [order_pg2, ← Nat.card_eq_fintype_card, GaloisField.card p k hk.ne']

/-! ## Counting consequences for a hypothetical plane of order 12 -/

/-- **Known result** (standard counting, Hughes–Piper, *Projective Planes*, Thm 3.3; here
reused from Mathlib's `card_points`, `card_lines`, `pointCount_eq`, `lineCount_eq`): a
projective plane of order 12, if one exists, has exactly 157 points and 157 lines, every line
has 13 points and every point lies on 13 lines. (This does not decide existence.) -/
theorem order_twelve_counts (P L : Type) [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Fintype L] (h : ProjectivePlane.order P L = 12) :
    Fintype.card P = 157 ∧ Fintype.card L = 157 ∧
      (∀ l : L, pointCount P l = 13) ∧ (∀ p : P, lineCount L p = 13) := by
  refine ⟨?_, ?_, fun l => ?_, fun p => ?_⟩
  · rw [ProjectivePlane.card_points P L, h]; norm_num
  · rw [ProjectivePlane.card_lines P L, h]; norm_num
  · rw [ProjectivePlane.pointCount_eq P l, h]
  · rw [ProjectivePlane.lineCount_eq L p, h]

#print axioms fano_order
#print axioms exists_plane_of_order_two
#print axioms order_pg2
#print axioms exists_plane_of_prime_power_order
#print axioms order_twelve_counts

end CryptoLean.OpenProblems.ProjectivePlanes
