# Conductor gap across an isogeny volcano: floor/crater algebra in Lean

2026-11-21. Module: [`CryptoLean/Curve/ConductorGap.lean`](../CryptoLean/Curve/ConductorGap.lean).
Receipts: [`receipts/ConductorGap20261121/`](receipts/ConductorGap20261121/)
(proof gate PASS, 268 theorems, 0 trusted; `InstanceProbe.lean`).
Exact check: [`checks/conductor-gap-20261121/`](checks/conductor-gap-20261121/).

## Question and what was open

The studies in `isogeny-labs/crypto` (`research/conductor_gap_cm_pairs_20261010`,
`conductor_gap_cm_orbits_20261015`, `deep_volcano_prime_gap_20261022`,
`conductor_gap_replication_20261025`; problem card
`problems/conductor-gap-upper-floor-and-cost.md`) ask whether ECDLP is
equally hard on both sides of a large prime `N` in the conductor of a
volcano's isogeny class (`S1`: `N ∤ c(E)`, the crater side; `S2`: `N ∣ c(E)`,
the floor side). They proved the transfer step in Lean over hand-rolled
`Hom` records (no group laws) and listed as **unformalized bridges**:
Kohel's "every isogeny across the gap has degree divisible by `N`", the
Frobenius action on `E[N]` that separates the sides, and the order
classification. This module proves the algebraic content of those bridges
over Mathlib structures, and reproves the transfer over real groups.

## Results (all proved, standard axioms only)

| # | declaration | statement | kind |
|:--|:--|:--|:--|
| 1 | `smul_conductorOrder_le_iff` | in `ℤ[ω]`, `d·O_f ⊆ O_g ↔ g ∣ d f` | law |
| 2 | `prime_dvd_degree_of_gap`, `…'` | `d·O_f ⊆ O_g`, prime `N ∣ g`, `N ∤ f` ⇒ `N ∣ d` (either direction) | law |
| 3 | `frobenius_scalar_iff` | `π = x + yω` acts on `O/NO` as scalar `λ` ⇔ `N ∣ y ∧ x ≡ λ` | law |
| 4 | `scalar_trace_congr` | a scalar Frobenius is `t/2`: `tr π ≡ 2λ (mod N)` | law |
| 5 | `frobenius_eigen_card_le` | `N ∤ y` ⇒ every eigenspace of `π` on `O/NO` has `≤ N` elements | law |
| 6 | `frobenius_eigen_card_full` | `N ∣ y` ⇒ the `x`-eigenspace is all `N²` elements | law |
| 7 | `orderEmbed`, `orderEmbed_apply`, `range_orderEmbed` | `O_c ≅ QuadraticAlgebra ℤ (c²a) (cb)`, image exactly `conductorOrder c`; Frobenius `x + fω = x + (f/c)ω_c` | instance obligation |
| 8 | `crater_side_full` | `N ∤ c`, `N ∣ f` ⇒ Frobenius eigenspace on `O_c/NO_c` is `(ZMod N)²` | endpoint |
| 9 | `floor_side_line` | `N ∣ c`, `N² ∤ f` ⇒ every Frobenius eigenspace on `O_c/NO_c` has `≤ N` elements | endpoint |
| 10 | `gap_prime_dvd_order` | `t² − 4p = Df²`, odd prime `N ∣ f`, `N ∣ p+1−t` ⇒ `N ∣ p−1`, `N ∣ t−2`, `N² ∣ p+1−t` | law |
| 11 | `dlog_transfer` | `φ : G →+ H`, `ψ ∘ φ = d•`, `gcd(d, ord P) = 1`, `Q ∈ ⟨P⟩`, `φQ = k•φP` ⇒ `Q = k•P` | law |
| 12 | `addOrderOf_map_eq` | same hypotheses ⇒ `ord φ(P) = ord P` | law |

Probe (`InstanceProbe.lean`): 11–12 applied unchanged to
`WeierstrassCurve.Affine.Point` (Mathlib's curve group); the 2026-10-22
class numbers (`t² − 4p = −11·(2⁶·631409)²`, `N ∣ t + 2`, `N ∤ #E`) by
`norm_num`/`decide`.

### What it says about hardness across the gap

* **Degree.** Any isogeny between the sides has `N ∣ deg` (2, given the
  bridge `d·End(E) ⊆ End(E')`). Transfer cost across the gap is therefore at
  least one degree-`N` step; for `N` large it is the dominant term (Vélu
  `O(N)`, √élu `Õ(√N)`, or Kani/Robert-style representations).
* **Where the sides differ.** Only in the `N`-part: via Lenstra's
  `E[N] ≅ O_c/NO_c`, the crater side has scalar Frobenius on `E[N]`
  (eigenvalue `t/2`), so `E(F_p)[N]` or its twist's is all of `(Z/N)²`;
  on the floor side every rational `N`-torsion subgroup is cyclic (8, 9).
* **Prime-order DLP subgroups are untouched.** For the DLP prime `n ≠ N`,
  `gcd(N^k·ℓ^j, n) = 1` and 11–12 carry every instance across with the
  answer and the subgroup order preserved, for every solver.
* **If the gap prime is the DLP prime, the whole class is pairing-weak.**
  `N ∣ f` and `N ∣ #E` force `N ∣ p − 1` (10): embedding degree one on
  every curve of the class, floor and crater alike. So a large-prime
  conductor gap never produces a floor/crater hardness split in the
  `N`-part either; at most it changes `E(F_p)[N^∞]` from `(Z/N)²·…` to cyclic.

Net: no ECDLP hardness gap between floor and crater is provable or present
in the algebra; the gap shows up only as (i) a lower bound `N ∣ deg` on the
cost of moving instances, and (ii) the shape of the `N`-torsion.

## Exact check (independent of Lean)

`python3 check_gap.py 5 1500`: every prime `p ≤ 1500`, every ordinary class
with `D0 ∉ {−3, −4}`, every odd `N ∥ f` with `N ∣ #E`; brute-force
`#E(F_p)[N]` on every curve (j-invariant) of the class.

| prediction | result |
|:--|:--|
| 10: `N ∣ p−1`, `N ∣ t−2`, `N² ∣ #E` | 1,233 / 1,233 cases |
| 8+9 via Lenstra: `#E(F_p)[N] ∈ {N, N²}` | 24,300 / 24,300 curves |
| class number: `#cyclic = (N − (D0/N))·#full` | 1,233 / 1,233 cases |
| negative control (`#cyclic = N·#full`) | fails 144 / 171 at `p ≤ 400` (the rest have `(D0/N) = 0`) |

Output: `checks/conductor-gap-20261121/full.json` (4 min, one core).

## Lean instance gate

1. **Structure above.** `QuadraticAlgebra ℤ a b` (Mathlib: ring, `trace`,
   `norm`, `mapRingHom`, `lift`, `finrank_eq_two`); `Subring`; `ZMod N`
   vector spaces; `AddCommGroup`, `AddMonoidHom`, `addOrderOf`.
2. **Theorems used as stated.** `Submodule.finrank_lt`,
   `Module.natCard_eq_pow_finrank`, `addOrderOf_dvd_iff_zsmul_eq_zero`,
   `addOrderOf_map_dvd`, `Nat.Coprime.addOrderOf_nsmul`,
   `IsCoprime.dvd_of_dvd_mul_left`, `Prime.dvd_of_dvd_pow`, `QuadraticAlgebra.lift`.
3. **Objects as instances.** Orders are `Subring`s of `ℤ[ω]` (and `O_c` is
   itself a `QuadraticAlgebra` via `orderEmbed`); `O/NO` is
   `QuadraticAlgebra (ZMod N) a b` via `mapRingHom`; curve groups are
   `WeierstrassCurve.Affine.Point` (probe).
4. **Assembly probe.** `InstanceProbe.lean` (compiles; axioms recorded).
5. **Missing components built.** Only `conductorOrder`, `reduce`,
   `orderEmbed`; no bound or law re-derived.
6. **Inheritance.** ring ops on orders: `Subring` (`mul_mem'` etc. proved
   once); trace/norm: Mathlib `QuadraticAlgebra.trace`; dimension 2:
   `finrank_eq_two`; group ops on points: Mathlib `AddCommGroup W.Point`.

No `maxHeartbeats`, no `native_decide`, no composite opened.

## Bridges still unformalized (named hypotheses, not proved)

* `End(E) ≅ O_c` inside `K = Q(√D0)`, `π ↦ (t + f√D0)/2` (Deuring/CM);
* `α ↦ φ α φ̂` identifies with `d·α` in `K`, so `d·End(E) ⊆ End(E')`
  (input to 2);
* `E[N] ≅ O_c/NO_c` as `O_c`-modules (Lenstra 1996; input to 8, 9);
* isogenies/duals as `W.Point →+ W'.Point` with `ψ ∘ φ = [d]` (input to 11);
* `#E(F_p) = p + 1 − t` (input to 10).

Mathlib has `WeierstrassCurve` and its point group but no isogenies or
endomorphism rings; these need that layer first.
