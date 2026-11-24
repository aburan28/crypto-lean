/-
Rule-out lemmas for the smooth-p+1 index-calculus study
(isogeny-labs trunk `docs/notes/smooth-pp1-ic-20261124/RESULTS.md`).

Study class: p prime, p ≡ 2 (mod 3), E : y² = x³ + 1 over F_p,
#E(F_p) = p + 1 − a, r prime with r ∣ #E(F_p) and r ∣ p + 1.

Every statement is a generic law (no study constant appears in a hypothesis);
the study's parameters are instances, exhibited in the `example`s at the end.

* L1 `supersingular_forcing`  : r ∣ p+1, r ∣ p+1−a, a² ≤ 4p, 4p < r² ⇒ a = 0.
* L2 `embedding_degree_two`   : r > 2, r ∣ p+1, p ≥ 2 ⇒ r ∤ p−1, r ∣ p²−1,
                                and orderOf (p : ZMod r) = 2 for r prime.
* L3 `cube_root_unity_eq_one` : p ≡ 2 (mod 3) ⇒ ζ³ = 1 → ζ = 1 in ZMod p;
     `scaling_preserves_iff`  : (x,y) ↦ (u x, ε y) preserves y² = x³ + 1 on
                                ZMod p ⇔ u = 1 ∧ (ε = 1 ∨ ε = −1);
     `variableChange_fixes_iff`: Mathlib's `VariableChange` C fixes the
                                Weierstrass curve y² = x³ + 1 over ZMod p
                                (p ≠ 2) ⇔ C = id or C = negation (u = −1).
* L4 `pow_eq_one_of_frobenius_fixed`, `algebraMap_pow_eq_one`,
     `sixth_root_pow_eq_one`  : the IC projection z ↦ z^((p²−1)/r) kills
                                F_p* and the sixth roots of unity.
* L5 `range_pow_card`, `range_pow_unique`, `dlog_split`: g ↦ g^s maps a
     cyclic group of order r·s (r ⊥ s) onto its unique subgroup of order r,
     and Q = P^k is solved exactly by the pair of subproblems
     (P^s, Q^s) (order r) and (P^r, Q^r) (order s).
* L6 `prime_dvd_mul_two_pow(_le)`: a prime r ∣ c·2^k is 2 or divides c, so
     r ≤ max 2 c (the family p = c·2^k − 1 only).
-/
import Mathlib

set_option autoImplicit false

namespace CryptoLean.SmoothPP1

/-! ## L1 supersingular forcing -/

/-- **L1** (RESULTS.md "Supersingular-forcing lemma"). If r divides both
`p + 1` and `#E = p + 1 − a`, Hasse `a² ≤ 4p` holds and `r² > 4p`, then
`a = 0`. Primality of `r` is not needed. -/
theorem supersingular_forcing {p r : ℕ} {a : ℤ}
    (h1 : (r : ℤ) ∣ (p : ℤ) + 1) (h2 : (r : ℤ) ∣ (p : ℤ) + 1 - a)
    (hasse : a ^ 2 ≤ 4 * (p : ℤ)) (hbig : 4 * (p : ℤ) < (r : ℤ) ^ 2) :
    a = 0 := by
  by_contra ha
  have hra : (r : ℤ) ∣ a := by
    have := dvd_sub h1 h2
    simpa using this
  have hle : (r : ℤ) ≤ |a| :=
    Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hra)
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have : (r : ℤ) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs a]
    exact pow_le_pow_left₀ hr0 hle 2
  linarith

/-- **L1, contrapositive**: an ordinary trace `a ≠ 0` with `r ∣ p+1` and
`r ∣ #E` forces `r² ≤ 4p`. -/
theorem sq_le_of_trace_ne_zero {p r : ℕ} {a : ℤ}
    (h1 : (r : ℤ) ∣ (p : ℤ) + 1) (h2 : (r : ℤ) ∣ (p : ℤ) + 1 - a)
    (hasse : a ^ 2 ≤ 4 * (p : ℤ)) (ha : a ≠ 0) :
    (r : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
  by_contra h
  exact ha (supersingular_forcing h1 h2 hasse (not_le.mp h))

/-! ## L2 embedding degree exactly 2 -/

/-- **L2** (RESULTS.md H1/H2, DESIGN.md "MOV into μ_r ⊂ F_{p²}*"). For
`r > 2`, `r ∣ p + 1` and `p ≥ 2` (natural-number subtraction): `r ∤ p − 1`
and `r ∣ p² − 1`. Primality of `r` is not needed here. -/
theorem embedding_degree_two {p r : ℕ} (hp : 2 ≤ p) (hr : 2 < r)
    (h : r ∣ p + 1) : ¬ r ∣ p - 1 ∧ r ∣ p ^ 2 - 1 := by
  refine ⟨fun h' => ?_, ?_⟩
  · have h2 : r ∣ 2 := by
      have := Nat.dvd_sub h h'
      rwa [show p + 1 - (p - 1) = 2 by omega] at this
    exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
  · rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by
      have := Nat.sq_sub_sq p 1
      simpa using this]
    exact Dvd.dvd.mul_right h _

/-- **L2, order form**: for a prime `r > 2` with `r ∣ p + 1`, the
multiplicative order of `p` modulo `r` (the embedding degree) is exactly 2. -/
theorem orderOf_natCast_eq_two {p r : ℕ} [Fact r.Prime] (hr : 2 < r)
    (h : r ∣ p + 1) : orderOf (p : ZMod r) = 2 := by
  have hp : (p : ZMod r) = -1 := by
    rw [eq_neg_iff_add_eq_zero]
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [hp, orderOf_neg_one, ZMod.ringChar_zmod_n]
  simp only [ite_eq_right_iff]
  omega

/-! ## L3 no F_p-rational order-3 automorphism -/

/-- **L3** (RESULTS.md "Sharp point (automorphism non-confounding)"). For
`p ≡ 2 (mod 3)` prime, the only cube root of unity in `ZMod p` is 1. -/
theorem cube_root_unity_eq_one {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2)
    {ζ : ZMod p} (h : ζ ^ 3 = 1) : ζ = 1 := by
  have hζ : ζ ≠ 0 := by
    rintro rfl
    simp at h
  have hcard : ζ ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hζ
  have hg : Nat.gcd 3 (p - 1) = 1 := by
    have : ¬ 3 ∣ p - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr this
  have := pow_gcd_eq_one.mpr ⟨h, hcard⟩
  rwa [hg, pow_one] at this

/-- **L3, map form**. On `ZMod p`, `p ≡ 2 (mod 3)`, the coordinate scaling
`(x, y) ↦ (u x, ε y)` maps every solution of `y² = x³ + 1` to a solution iff
`u = 1` and `ε = ±1`: in this family only `±1` are F_p-rational. -/
theorem scaling_preserves_iff {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2)
    (u ε : ZMod p) :
    (∀ x y : ZMod p, y ^ 2 = x ^ 3 + 1 → (ε * y) ^ 2 = (u * x) ^ 3 + 1) ↔
      u = 1 ∧ (ε = 1 ∨ ε = -1) := by
  constructor
  · intro h
    have hu : u = 1 := by
      have := h (-1) 0 (by ring)
      apply cube_root_unity_eq_one hp3
      linear_combination this
    refine ⟨hu, ?_⟩
    have := h 0 1 (by ring)
    have hε : ε ^ 2 = 1 := by simpa using this
    exact mul_self_eq_one_iff.mp (by rw [← sq]; exact hε)
  · rintro ⟨rfl, hε | hε⟩ x y hxy <;> subst hε <;> linear_combination hxy

/-- The study curve `y² = x³ + 1` as a Mathlib Weierstrass curve. -/
def jZeroCurve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, 0, 1⟩

/-- Negation `(x, y) ↦ (x, −y)` as a Mathlib variable change (u = −1). -/
def negChange (R : Type*) [CommRing R] : WeierstrassCurve.VariableChange R :=
  ⟨-1, 0, 0, 0⟩

/-- **L3, Mathlib automorphism form**. Over `ZMod p` with `p` prime,
`p ≠ 2`, `p ≡ 2 (mod 3)`, an admissible change of variables
`(X, Y) ↦ (u²X + r, u³Y + u²sX + t)` (Mathlib `VariableChange`) fixes
`y² = x³ + 1` iff it is the identity or negation: the F_p-rational
automorphisms of E fixing O are exactly ±1. -/
theorem variableChange_fixes_iff {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp3 : p % 3 = 2) (C : WeierstrassCurve.VariableChange (ZMod p)) :
    C • jZeroCurve (ZMod p) = jZeroCurve (ZMod p) ↔
      C = 1 ∨ C = negChange (ZMod p) := by
  have hpp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp this
    exact hp2 this
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp this
    omega
  constructor
  · intro h
    have e1 := congrArg WeierstrassCurve.a₁ h
    have e2 := congrArg WeierstrassCurve.a₂ h
    have e3 := congrArg WeierstrassCurve.a₃ h
    have e6 := congrArg WeierstrassCurve.a₆ h
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₆, jZeroCurve]
      at e1 e2 e3 e6
    have hu0 : ((C.u⁻¹ : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
    have hs : C.s = 0 := by
      have hX := (mul_eq_zero.mp e1).resolve_left hu0
      exact (mul_eq_zero.mp (by linear_combination hX : (2 : ZMod p) * C.s = 0)).resolve_left h2
    have hr : C.r = 0 := by
      have hX := (mul_eq_zero.mp e2).resolve_left (pow_ne_zero _ hu0)
      rw [hs] at hX
      exact (mul_eq_zero.mp (by linear_combination hX : (3 : ZMod p) * C.r = 0)).resolve_left h3
    have ht : C.t = 0 := by
      have hX := (mul_eq_zero.mp e3).resolve_left (pow_ne_zero _ hu0)
      rw [hr] at hX
      exact (mul_eq_zero.mp (by linear_combination hX : (2 : ZMod p) * C.t = 0)).resolve_left h2
    have hw : ((C.u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 6 = 1 := by
      rw [hr, ht] at e6
      linear_combination e6
    have hw2 : (((C.u⁻¹ : (ZMod p)ˣ) : ZMod p) ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact hw
    have hsq := cube_root_unity_eq_one hp3 hw2
    rw [sq, mul_self_eq_one_iff] at hsq
    rcases hsq with hu | hu
    · left
      have : C.u = 1 := by
        have : C.u⁻¹ = 1 := Units.ext hu
        simpa using this
      exact WeierstrassCurve.VariableChange.ext this hr hs ht
    · right
      have : C.u = -1 := by
        have : C.u⁻¹ = -1 := Units.ext (by rw [Units.val_neg, Units.val_one]; exact hu)
        rw [← inv_inv C.u, this, inv_neg, inv_one]
      exact WeierstrassCurve.VariableChange.ext this hr hs ht
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · rw [WeierstrassCurve.variableChange_def]
      ext <;> norm_num [negChange, jZeroCurve]

/-! ## L4 the IC projection kills F_p* and the units of Z[ω] -/

/-- `(p² − 1)/r = (p − 1)·((p + 1)/r)` when `r ∣ p + 1` (natural numbers). -/
theorem sq_sub_one_div_eq {p r : ℕ} (hr : r ∣ p + 1) :
    (p ^ 2 - 1) / r = (p - 1) * ((p + 1) / r) := by
  have : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have := Nat.sq_sub_sq p 1
    simp only [one_pow] at this
    rw [this, mul_comm]
  rw [this, Nat.mul_div_assoc _ hr]

/-- **L4a** (GFP2_IC_RESULTS.md step 2, "Φ kills F_p*"). In any field, a
nonzero `x` fixed by `x ↦ x^p` (`p ≥ 1`) satisfies `x^((p²−1)/r) = 1`
whenever `r ∣ p + 1`. No hypothesis `r ∤ p − 1` is needed. -/
theorem pow_eq_one_of_frobenius_fixed {K : Type*} [Field K] {p r : ℕ}
    (hp : 1 ≤ p) (hr : r ∣ p + 1) {x : K} (hx0 : x ≠ 0) (hx : x ^ p = x) :
    x ^ ((p ^ 2 - 1) / r) = 1 := by
  have h1 : x ^ (p - 1) = 1 := by
    have := pow_sub_one_mul (by omega : p ≠ 0) x
    rw [hx] at this
    exact mul_eq_right₀ hx0 |>.mp this
  rw [sq_sub_one_div_eq hr, pow_mul, h1, one_pow]

/-- **L4a, prime-field form**: the image of a nonzero element of `ZMod p`
(for instance an inert rational prime) in any `ZMod p`-algebra field `K`,
e.g. `GF(p²)`, is killed by `z ↦ z^((p²−1)/r)` when `r ∣ p + 1`. -/
theorem algebraMap_pow_eq_one {K : Type*} [Field K] {p r : ℕ} [Fact p.Prime]
    [Algebra (ZMod p) K] (hr : r ∣ p + 1) {y : ZMod p} (hy : y ≠ 0) :
    (algebraMap (ZMod p) K y) ^ ((p ^ 2 - 1) / r) = 1 := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  refine pow_eq_one_of_frobenius_fixed hp hr ?_ ?_
  · exact (map_ne_zero _).mpr hy
  · rw [← map_pow, ZMod.pow_card]

/-- **L4b** (GFP2_IC_RESULTS.md step 2, "Φ kills units"). In any monoid, a
sixth root of unity is killed by `z ↦ z^((p²−1)/r)` when `6 ∣ p + 1`,
`r ∣ p + 1` and `gcd(6, r) = 1`. -/
theorem sixth_root_pow_eq_one {M : Type*} [Monoid M] {p r : ℕ}
    (h6 : 6 ∣ p + 1) (hr : r ∣ p + 1) (hcop : Nat.Coprime 6 r) {ζ : M}
    (hζ : ζ ^ 6 = 1) : ζ ^ ((p ^ 2 - 1) / r) = 1 := by
  have hq : 6 ∣ (p + 1) / r := by
    obtain ⟨q, hq⟩ := hr
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0; simp at hq
    rw [hq, Nat.mul_div_cancel_left _ hpos]
    exact hcop.dvd_of_dvd_mul_left (hq ▸ h6)
  obtain ⟨m, hm⟩ : 6 ∣ (p - 1) * ((p + 1) / r) := Dvd.dvd.mul_left hq _
  rw [sq_sub_one_div_eq hr, hm, pow_mul, hζ, one_pow]

/-- **L4b, study form**: `p` prime, `p ≠ 2`, `p ≡ 2 (mod 3)`, `r` prime,
`r > 3`, `r ∣ p + 1`. -/
theorem sixth_root_pow_eq_one_of_prime {M : Type*} [Monoid M] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p % 3 = 2) (hrp : r.Prime) (hr3 : 3 < r)
    (hr : r ∣ p + 1) {ζ : M} (hζ : ζ ^ 6 = 1) : ζ ^ ((p ^ 2 - 1) / r) = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h6 : 6 ∣ p + 1 := by omega
  have hcop : Nat.Coprime 6 r := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hrp).mpr ?_)
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases r <;> simp_all (config := {decide := true})
  exact sixth_root_pow_eq_one h6 hr hcop hζ

/-! ## L5 smoothness of s does not enter the order-r subproblem -/

section Cyclic

variable {G : Type*} [CommGroup G] {r s : ℕ}

/-- **L5a**: in a group of order `r·s` with `r ⊥ s`, the image of `g ↦ g^s`
is exactly the `r`-torsion `{g | g^r = 1}`. -/
theorem mem_range_pow_iff [Finite G] (hcard : Nat.card G = r * s)
    (hcop : r.Coprime s) (g : G) :
    g ∈ (powMonoidHom s : G →* G).range ↔ g ^ r = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hcard, pow_card_eq_one']
  · intro hg
    refine ⟨g ^ (Nat.gcdB r s), ?_⟩
    simp only [powMonoidHom_apply]
    have hab := Nat.gcd_eq_gcd_ab r s
    rw [hcop.gcd_eq_one, Nat.cast_one] at hab
    calc (g ^ (Nat.gcdB r s)) ^ s
        = (g ^ r) ^ (Nat.gcdA r s) * (g ^ (Nat.gcdB r s)) ^ s := by rw [hg, one_zpow, one_mul]
      _ = g ^ ((r : ℤ) * Nat.gcdA r s + (s : ℤ) * Nat.gcdB r s) := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast,
            ← zpow_natCast (g ^ r.gcdB s) s, ← zpow_mul, ← zpow_natCast g s, ← zpow_mul,
            mul_comm (r.gcdB s)]
      _ = g := by rw [← hab, zpow_one]

/-- **L5b**: for `G` cyclic of order `r·s` with `r ⊥ s`, the image of
`g ↦ g^s` has exactly `r` elements. -/
theorem card_range_pow [Finite G] [IsCyclic G] (hcard : Nat.card G = r * s) :
    Nat.card (powMonoidHom s : G →* G).range = r := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hs : s ≠ 0 := by
    rintro rfl
    simp at hcard
    exact (Nat.card_pos (α := G)).ne' hcard
  have htop : (⊤ : Subgroup G) = Subgroup.zpowers g :=
    (eq_top_iff.mpr fun x _ => hg x).symm
  rw [MonoidHom.range_eq_map, htop, MonoidHom.map_zpowers, Nat.card_zpowers,
    powMonoidHom_apply, orderOf_pow_of_dvd hs, orderOf_eq_card_of_forall_mem_zpowers hg,
    hcard, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)]
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  exact dvd_mul_left _ _

/-- **L5c**: the image of `g ↦ g^s` is the *unique* subgroup of order `r`. -/
theorem range_pow_unique [Finite G] [IsCyclic G] (hcard : Nat.card G = r * s)
    (hcop : r.Coprime s) (H : Subgroup G) (hH : Nat.card H = r) :
    H = (powMonoidHom s : G →* G).range := by
  refine Subgroup.eq_of_le_of_card_ge (fun h hh => ?_) ?_
  · rw [mem_range_pow_iff hcard hcop, ← hH]
    have := pow_card_eq_one' (x := (⟨h, hh⟩ : H))
    exact congrArg Subtype.val this
  · rw [card_range_pow hcard, hH]

end Cyclic

/-- **L5d** (RESULTS.md H0 "smoothness of s only feeds Pohlig–Hellman on the
s-part"). Let `P` have order `r·s` with `r ⊥ s`, `r, s ≠ 0`, and `Q = P^k`.
Then `k'` solves `P^k' = Q` iff it solves both projected problems
`(P^s)^k' = Q^s` (in the order-`r` subgroup) and `(P^r)^k' = Q^r` (order `s`).
Nothing about the factorisation of `s` enters. -/
theorem dlog_split {G : Type*} [Group G] {r s : ℕ} (hr : r ≠ 0) (hs : s ≠ 0)
    (hcop : r.Coprime s) {P Q : G} (hP : orderOf P = r * s) {k : ℕ}
    (hQ : Q = P ^ k) (k' : ℕ) :
    P ^ k' = Q ↔ (P ^ s) ^ k' = Q ^ s ∧ (P ^ r) ^ k' = Q ^ r := by
  have hPs : orderOf (P ^ s) = r := by
    rw [orderOf_pow_of_dvd hs (hP ▸ dvd_mul_left _ _), hP,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)]
  have hPr : orderOf (P ^ r) = s := by
    rw [orderOf_pow_of_dvd hr (hP ▸ dvd_mul_right _ _), hP,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr)]
  subst hQ
  rw [← pow_mul P k s, mul_comm k s, pow_mul, ← pow_mul P k r, mul_comm k r, pow_mul,
    pow_eq_pow_iff_modEq, pow_eq_pow_iff_modEq, pow_eq_pow_iff_modEq, hPs, hPr, hP,
    Nat.modEq_and_modEq_iff_modEq_mul hcop]

/-- **L5e**: `k mod r` is determined by the pair `(P^s, Q^s)` alone. -/
theorem dlog_mod_r {G : Type*} [Group G] {r s : ℕ} (hs : s ≠ 0)
    {P Q : G} (hP : orderOf P = r * s) {k : ℕ} (hQ : Q = P ^ k) (k' : ℕ) :
    (P ^ s) ^ k' = Q ^ s ↔ k' ≡ k [MOD r] := by
  have hPs : orderOf (P ^ s) = r := by
    rw [orderOf_pow_of_dvd hs (hP ▸ dvd_mul_left _ _), hP,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hs)]
  subst hQ
  rw [← pow_mul P k s, mul_comm k s, pow_mul, pow_eq_pow_iff_modEq, hPs]

/-! ## L6 the family p = c·2^k − 1 has no large prime in p + 1 -/

/-- **L6** (RESULTS.md H0 "if p+1 were fully smooth the ECDLP is trivially
PH-solvable"). Every prime `r ∣ c·2^k` is `2` or divides `c`. Stated for the
family `p + 1 = c·2^k` only; it is false for sparse `p` in general
(`p = 2^64 − 59`: `p + 1` has a 59-bit prime factor). -/
theorem prime_dvd_mul_two_pow {r c k : ℕ} (hr : r.Prime) (h : r ∣ c * 2 ^ k) :
    r = 2 ∨ r ∣ c := by
  rcases (Nat.Prime.dvd_mul hr).mp h with hc | h2
  · exact Or.inr hc
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))

/-- **L6, size form**: for `c ≠ 0`, every prime `r ∣ c·2^k` has `r ≤ max 2 c`,
so the MOV subgroup order is at most `max 2 c`. -/
theorem prime_dvd_mul_two_pow_le {r c k : ℕ} (hr : r.Prime) (hc : c ≠ 0)
    (h : r ∣ c * 2 ^ k) : r ≤ max 2 c := by
  rcases prime_dvd_mul_two_pow hr h with rfl | hrc
  · exact le_max_left _ _
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hrc).trans (le_max_right _ _)

/-! ## Satisfiability: the study instance p = 173 = 6·29 − 1, r = 29, s = 6 -/

section Instance

local instance fact173 : Fact (Nat.Prime 173) := ⟨by norm_num⟩
local instance fact29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- L1 hypotheses hold at p = 173, r = 29, a = 0 (29² = 841 > 692 = 4p). -/
example : ((29 : ℕ) : ℤ) ∣ ((173 : ℕ) : ℤ) + 1 ∧ ((29 : ℕ) : ℤ) ∣ ((173 : ℕ) : ℤ) + 1 - 0 ∧
    (0 : ℤ) ^ 2 ≤ 4 * ((173 : ℕ) : ℤ) ∧ 4 * ((173 : ℕ) : ℤ) < ((29 : ℕ) : ℤ) ^ 2 := by
  norm_num

/-- Non-vacuity of L1: a = 29 meets both divisibilities but not Hasse. -/
example : ((29 : ℕ) : ℤ) ∣ ((173 : ℕ) : ℤ) + 1 - 29 ∧ ¬ (29 : ℤ) ^ 2 ≤ 4 * ((173 : ℕ) : ℤ) := by
  norm_num

/-- L1 is not provable without `r² > 4p`: r = 3, a = 3, p = 173. -/
example : ((3 : ℕ) : ℤ) ∣ ((173 : ℕ) : ℤ) + 1 ∧ ((3 : ℕ) : ℤ) ∣ ((173 : ℕ) : ℤ) + 1 - 3 ∧
    (3 : ℤ) ^ 2 ≤ 4 * ((173 : ℕ) : ℤ) := by norm_num

example : ¬ 29 ∣ 173 - 1 ∧ 29 ∣ 173 ^ 2 - 1 :=
  embedding_degree_two (by norm_num) (by norm_num) (by norm_num)

example : orderOf ((173 : ℕ) : ZMod 29) = 2 :=
  orderOf_natCast_eq_two (by norm_num) (by norm_num)

example (ζ : ZMod 173) (h : ζ ^ 3 = 1) : ζ = 1 := cube_root_unity_eq_one (by norm_num) h

example (C : WeierstrassCurve.VariableChange (ZMod 173)) :
    C • jZeroCurve (ZMod 173) = jZeroCurve (ZMod 173) ↔ C = 1 ∨ C = negChange (ZMod 173) :=
  variableChange_fixes_iff (by norm_num) (by norm_num) C

/-- L4b at the study instance: units of Z[ω] die in `GF(173²)`. -/
example (ζ : GaloisField 173 2) (h : ζ ^ 6 = 1) : ζ ^ ((173 ^ 2 - 1) / 29) = 1 :=
  sixth_root_pow_eq_one_of_prime (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) h

/-- L4a at the study instance, in `GF(173²)`. -/
example (y : ZMod 173) (hy : y ≠ 0) :
    (algebraMap (ZMod 173) (GaloisField 173 2) y) ^ ((173 ^ 2 - 1) / 29) = 1 :=
  algebraMap_pow_eq_one (by norm_num) hy

/-- L5 at the study instance: `ZMod 174` written multiplicatively, r = 29, s = 6. -/
example : Nat.card ((powMonoidHom 6 : Multiplicative (ZMod 174) →* _).range) = 29 :=
  card_range_pow (by simp)

/-- L5 at the study instance: `k = 100` is recovered from its two projections. -/
example (P : Multiplicative (ZMod 174)) (hP : orderOf P = 29 * 6) (k' : ℕ) :
    P ^ k' = P ^ 100 ↔ (P ^ 6) ^ k' = (P ^ 100) ^ 6 ∧ (P ^ 29) ^ k' = (P ^ 100) ^ 29 :=
  dlog_split (by norm_num) (by norm_num) (by norm_num) hP rfl k'

/-- The hypothesis `orderOf P = r·s` of L5d is met by the generator of `ZMod 174`. -/
example : orderOf (Multiplicative.ofAdd (1 : ZMod 174)) = 29 * 6 := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- L6 instance: p = 3·2^5 − 1 = 95 + 1 = 96; the prime 3 divides c = 3. -/
example : (3 : ℕ) = 2 ∨ 3 ∣ 3 := prime_dvd_mul_two_pow (k := 5) (by norm_num) (by norm_num)

end Instance

end CryptoLean.SmoothPP1
