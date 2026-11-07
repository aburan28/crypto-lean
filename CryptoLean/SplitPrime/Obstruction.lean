-- Formalizes the group-theoretic and polynomial cores of
-- aburan28/crypto research/split_prime_ecdlp_20261107 (README §3, and the Lean
-- obligations of proposals P1 and P2 in its §6). Elliptic curves, isogenies and
-- Shoup's generic-group bound are NOT formalized here.
import Mathlib.Algebra.Polynomial.Div
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace CryptoLean.SplitPrime

open Polynomial

/-- Scalar-only action, item 2 (README §3 of `split_prime_ecdlp_20261107`): every
endomorphism of a cyclic additive group is multiplication by an integer. Applied to
`E(F_p)`, cyclic of prime order, every `α ∈ End(E)` acts as a scalar. Does not
identify which scalar (Lenstra's `E(F_p) ≅ O/(π − 1)` is not formalized). -/
theorem endo_cyclic_eq_zsmul {G : Type*} [AddCommGroup G] [IsAddCyclic G] (f : G →+ G) :
    ∃ s : ℤ, ∀ x, f x = s • x := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := G)
  obtain ⟨s, hs⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg (f g))
  refine ⟨s, fun x => ?_⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg x)
  rw [map_zsmul, ← hs, smul_smul, smul_smul, mul_comm]

/-- Scalar-only action, item 1: a nonzero homomorphism between finite additive groups
of the same prime order is bijective (and, being a homomorphism, commutes with every
`k •`). Applied to an isogeny `φ : E → E'` restricted to `E(F_p)` whose kernel does not
contain `E(F_p)` (for example `deg φ` prime to `n`), a DLP instance transports with the
same answer. The isogeny itself is not formalized. -/
theorem hom_card_prime_bijective {G H : Type*} [AddGroup G] [AddGroup H] [Finite G]
    [Finite H] {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) (hH : Nat.card H = p)
    (f : G →+ H) (hf : f ≠ 0) : Function.Bijective f := by
  have hker : Nat.card f.ker ∣ p := hG ▸ AddSubgroup.card_addSubgroup_dvd_card f.ker
  rcases (Nat.dvd_prime hp).1 hker with h1 | hpk
  · have hbot : f.ker = ⊥ := AddSubgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective f := (AddMonoidHom.ker_eq_bot_iff f).1 hbot
    exact (Function.Injective.bijective_of_nat_card_le hinj (by rw [hG, hH]))
  · exfalso
    apply hf
    have htop : f.ker = ⊤ := AddSubgroup.eq_top_of_card_eq _ (by rw [hpk, hG])
    ext x
    have hx : x ∈ f.ker := htop ▸ AddSubgroup.mem_top x
    simpa using hx

/-- Purity lemma of proposal P2 (`split_prime_ecdlp_20261107` §6): if `π` (Frobenius)
fixes the `E`-points and negates the twist points, the relation's sum `R` is fixed by
`π`, and `π` has no nonzero fixed point of order dividing 2, then the twist summands sum
to zero. On a prime-order curve the hypothesis `h2` holds because `E(F_p)[2] = 0`. -/
theorem twist_part_sum_eq_zero {G ι : Type*} [AddCommGroup G] (π : G →+ G)
    (h2 : ∀ x, π x = x → 2 • x = 0 → x = 0)
    (s : Finset ι) (P : ι → G) (η : ι → Bool)
    (hP : ∀ i ∈ s, π (P i) = if η i then P i else -P i)
    (hR : π (∑ i ∈ s, P i) = ∑ i ∈ s, P i) :
    ∑ i ∈ s.filter (fun i => η i = false), P i = 0 := by
  set S := ∑ i ∈ s.filter (fun i => η i = false), P i with hSdef
  set T := ∑ i ∈ s.filter (fun i => ¬ η i = false), P i with hTdef
  have hsum : ∑ i ∈ s, P i = S + T :=
    (Finset.sum_filter_add_sum_filter_not s (fun i => η i = false) P).symm
  have hπS : π S = -S := by
    rw [hSdef, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hP i hi.1, hi.2]
    rfl
  have hπT : π T = T := by
    rw [hTdef, map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    have : η i = true := by simpa using hi.2
    rw [hP i hi.1, this]
    rfl
  rw [hsum, map_add, hπS, hπT] at hR
  have hneg : -S = S := add_right_cancel hR
  have h2S : 2 • S = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel S
  exact h2 S (by rw [hπS, hneg]) h2S

section Towers

variable {F : Type*} [Field F]

/-- `dick j` is the Dickson polynomial of index `2 ^ j`: `D₁ = X`, `D_{2k} = D_k² − 2`. -/
noncomputable def dick : ℕ → F[X]
  | 0 => X
  | j + 1 => dick j ^ 2 - 2

/-- The quadratic remainder tower of proposal P1: `V₀ = X mod U`,
`V_{j+1} = (V_j² − 2) mod U`. -/
noncomputable def dickTower (U : F[X]) : ℕ → F[X]
  | 0 => X %ₘ U
  | j + 1 => (dickTower U j ^ 2 - 2) %ₘ U

/-- The Kummer tower: `W₀ = X mod U`, `W_{j+1} = W_j² mod U`. -/
noncomputable def kumTower (U : F[X]) : ℕ → F[X]
  | 0 => X %ₘ U
  | j + 1 => (kumTower U j ^ 2) %ₘ U

theorem modByMonic_sq_sub_two {U a : F[X]} (hU : U.Monic) :
    ((a %ₘ U) ^ 2 - 2) %ₘ U = (a ^ 2 - 2) %ₘ U := by
  apply modByMonic_eq_of_dvd_sub hU
  have hd : U ∣ a %ₘ U - a := by
    rw [modByMonic_eq_sub_mul_div a U]
    exact ⟨-(a /ₘ U), by ring⟩
  have : (a %ₘ U) ^ 2 - 2 - (a ^ 2 - 2) = (a %ₘ U - a) * (a %ₘ U + a) := by ring
  rw [this]
  exact dvd_mul_of_dvd_left hd _

theorem modByMonic_sq {U a : F[X]} (hU : U.Monic) :
    ((a %ₘ U) ^ 2) %ₘ U = (a ^ 2) %ₘ U := by
  apply modByMonic_eq_of_dvd_sub hU
  have hd : U ∣ a %ₘ U - a := by
    rw [modByMonic_eq_sub_mul_div a U]
    exact ⟨-(a /ₘ U), by ring⟩
  have : (a %ₘ U) ^ 2 - a ^ 2 = (a %ₘ U - a) * (a %ₘ U + a) := by ring
  rw [this]
  exact dvd_mul_of_dvd_left hd _

/-- The remainder tower computes the remainder of the Dickson polynomial. -/
theorem dickTower_eq {U : F[X]} (hU : U.Monic) : ∀ j, dickTower U j = dick j %ₘ U
  | 0 => rfl
  | j + 1 => by
    rw [dickTower, dickTower_eq hU j, dick]
    exact modByMonic_sq_sub_two hU

theorem kumTower_eq {U : F[X]} (hU : U.Monic) : ∀ j, kumTower U j = (X ^ (2 ^ j)) %ₘ U
  | 0 => by simp [kumTower]
  | j + 1 => by
    rw [kumTower, kumTower_eq hU j, modByMonic_sq hU, ← pow_mul, pow_succ]

theorem modByMonic_eq_C_iff {U a : F[X]} (hU : U.Monic) (hdeg : 1 ≤ U.natDegree) (c : F) :
    a %ₘ U = C c ↔ U ∣ a - C c := by
  have hC : (C c) %ₘ U = C c := by
    rw [modByMonic_eq_self_iff hU]
    calc degree (C c) ≤ 0 := degree_C_le
      _ < degree U := by
        rw [degree_eq_natDegree hU.ne_zero]
        exact_mod_cast hdeg
  constructor
  · intro h
    have h' := modByMonic_eq_sub_mul_div a U
    rw [h] at h'
    refine ⟨a /ₘ U, ?_⟩
    rw [h']
    ring
  · intro h
    rw [modByMonic_eq_of_dvd_sub hU h, hC]

/-- Faithfulness of the Dickson membership tower (proposal P1's Lean obligation): for
`U` monic of degree at least one, the quadratic remainder tower ends at the constant `c`
exactly when `U ∣ D_{2^t}(X) − c`, i.e. every root of `U` lies in the Dickson base. -/
theorem dickson_tower_faithful {U : F[X]} (hU : U.Monic) (hdeg : 1 ≤ U.natDegree)
    (t : ℕ) (c : F) : dickTower U t = C c ↔ U ∣ dick t - C c := by
  rw [dickTower_eq hU]
  exact modByMonic_eq_C_iff hU hdeg c

/-- Faithfulness of the Kummer membership tower: `W_t = c` exactly when
`U ∣ X^{2^t} − c`. -/
theorem kummer_tower_faithful {U : F[X]} (hU : U.Monic) (hdeg : 1 ≤ U.natDegree)
    (t : ℕ) (c : F) : kumTower U t = C c ↔ U ∣ X ^ (2 ^ t) - C c := by
  rw [kumTower_eq hU]
  exact modByMonic_eq_C_iff hU hdeg c

end Towers

end CryptoLean.SplitPrime
