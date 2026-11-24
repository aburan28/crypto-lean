# Smooth-p+1 index calculus: rule-out lemmas in Lean

2026-11-24. Module: [`CryptoLean/Curve/SmoothPP1RuleOut.lean`](../CryptoLean/Curve/SmoothPP1RuleOut.lean),
namespace `CryptoLean.SmoothPP1`.
Receipts: [`receipts/SmoothPP1RuleOut20261124/`](receipts/SmoothPP1RuleOut20261124/)
(`tools/proof-gate.sh`, whole repository).
Consumer: isogeny-labs trunk `docs/notes/smooth-pp1-ic-20261124/` (`RESULTS.md`,
`GFP2_IC_RESULTS.md`, `DESIGN.md`).

Study class: `p` prime, `p ≡ 2 (mod 3)`, `E : y² = x³ + 1` over `F_p`,
`#E(F_p) = p + 1 − a`, `r` prime, `r ∣ p + 1`, `r ∣ #E(F_p)`. Every theorem below
is a generic law; the study's parameters (`p = 173 = 6·29 − 1`, `r = 29`, `s = 6`)
appear only in the `example`s at the end of the module (satisfiability of every
hypothesis set, and non-vacuity of L1).

Pinned: Lean `v4.35.0`, Mathlib `cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`.
Build: `lake exe cache get && lake build CryptoLean.Curve.SmoothPP1RuleOut`;
gate: `tools/proof-gate.sh --out <dir>`.

## Statements ↔ claims

| # | Lean | English claim | used in |
|:--|:--|:--|:--|
| L1 | `supersingular_forcing` | `(r:ℤ) ∣ p+1`, `(r:ℤ) ∣ p+1−a`, `a² ≤ 4p`, `4p < r²` ⇒ `a = 0` | RESULTS.md "Supersingular-forcing lemma" |
| L1′ | `sq_le_of_trace_ne_zero` | same divisibilities, Hasse, `a ≠ 0` ⇒ `r² ≤ 4p` | same ("ordinary k = 2 only with r ≤ 2√p") |
| L2 | `embedding_degree_two` | `p ≥ 2`, `r > 2`, `r ∣ p+1` ⇒ `¬ r ∣ p−1 ∧ r ∣ p²−1` (ℕ, truncated `−` safe since `p ≥ 2`) | DESIGN.md MOV into μ_r ⊂ F_{p²}*; RESULTS.md H1/H2 |
| L2′ | `orderOf_natCast_eq_two` | `r` prime, `r > 2`, `r ∣ p+1` ⇒ `orderOf (p : ZMod r) = 2` (embedding degree exactly 2) | same |
| L3 | `cube_root_unity_eq_one` | `p` prime, `p % 3 = 2`, `ζ : ZMod p`, `ζ³ = 1` ⇒ `ζ = 1` | RESULTS.md "Sharp point (automorphism non-confounding)" |
| L3′ | `scaling_preserves_iff` | over `ZMod p`, `p % 3 = 2`: `(x,y) ↦ (u x, ε y)` maps every solution of `y² = x³+1` to a solution ⇔ `u = 1 ∧ (ε = 1 ∨ ε = −1)` | same |
| L3″ | `variableChange_fixes_iff` | `p` prime, `p ≠ 2`, `p % 3 = 2`: a Mathlib `WeierstrassCurve.VariableChange` `C` satisfies `C • (y²=x³+1) = (y²=x³+1)` ⇔ `C = 1 ∨ C = negChange` (u = −1, r = s = t = 0) | same: the F_p-rational automorphisms (fixing O) are exactly ±1 |
| L4a | `pow_eq_one_of_frobenius_fixed` | any field `K`, `p ≥ 1`, `r ∣ p+1`, `x ≠ 0`, `x^p = x` ⇒ `x^((p²−1)/r) = 1` | GFP2_IC_RESULTS.md step 2 "Φ kills F_p*", "inert primes contribute nothing" |
| L4a′ | `algebraMap_pow_eq_one` | `K` a `ZMod p`-algebra field, `r ∣ p+1`, `y ≠ 0` in `ZMod p` ⇒ `(algebraMap y)^((p²−1)/r) = 1` | same |
| L4b | `sixth_root_pow_eq_one` | any monoid, `6 ∣ p+1`, `r ∣ p+1`, `gcd(6,r)=1`, `ζ⁶ = 1` ⇒ `ζ^((p²−1)/r) = 1` | GFP2_IC_RESULTS.md "Φ kills units" (Z[ω]* = μ₆) |
| L4b′ | `sixth_root_pow_eq_one_of_prime` | study form: `p` prime ≠ 2, `p % 3 = 2`, `r` prime > 3, `r ∣ p+1` | same |
| L5a | `mem_range_pow_iff` | finite comm. group, `card = r·s`, `r ⊥ s`: `g ∈ range (·^s) ⇔ g^r = 1` | RESULTS.md H0 |
| L5b | `card_range_pow` | cyclic, `card = r·s`: `card (range (·^s)) = r` | H0 |
| L5c | `range_pow_unique` | cyclic, `card = r·s`, `r ⊥ s`: every subgroup of order `r` equals `range (·^s)` | H0 |
| L5d | `dlog_split` | any group, `orderOf P = r·s`, `r ⊥ s`, `r,s ≠ 0`, `Q = P^k`: `P^k' = Q ⇔ (P^s)^k' = Q^s ∧ (P^r)^k' = Q^r` | H0 "smoothness of s only feeds Pohlig–Hellman on the s-part" |
| L5e | `dlog_mod_r` | `orderOf P = r·s`, `s ≠ 0`, `Q = P^k`: `(P^s)^k' = Q^s ⇔ k' ≡ k [MOD r]` | H0 (k mod r is fixed by (P^s, Q^s) alone) |

## Fidelity table (formal vs claim)

| claim | Lean | weaker or different in Lean |
|:--|:--|:--|
| L1 | `supersingular_forcing` | Hasse is a hypothesis (`a² ≤ 4p` over ℤ), not derived from E; `#E = p+1−a` is encoded only through `r ∣ p+1−a`. **Stronger** than asked: `r` prime not needed |
| L2 | `embedding_degree_two`, `orderOf_natCast_eq_two` | none; primality of `r` only needed for the order form |
| L3 | `cube_root_unity_eq_one` | none |
| L3 "only ±1" | `scaling_preserves_iff`, `variableChange_fixes_iff` | covers all admissible Weierstrass changes of variables (Mathlib's `VariableChange`), i.e. automorphisms fixing O given by coordinate changes; it does not quantify over arbitrary morphisms of `E.Point`. `p ≠ 2` needed in L3″ (y² = x³+1 is singular in char 2) |
| L4 | `pow_eq_one_of_frobenius_fixed`, `algebraMap_pow_eq_one`, `sixth_root_pow_eq_one*` | **Stronger**: `r ∤ p−1` and `|K| = p²` are not needed; any field. Units: the lemma is about sixth roots of unity in the target; that the image of Z[ω]* lands in μ₆ is the ring-hom fact, not stated |
| L5 | `mem_range_pow_iff` … `dlog_mod_r` | algebraic reduction only; no cost statement. The CRT step is Mathlib's `Nat.modEq_and_modEq_iff_modEq_mul` (ZMod form `ZMod.chineseRemainder` not used). No generic-group-model Ω(√r) lower bound: none exists in crypto-lean (README "Not yet in v0.1.0"); out of scope |

## Instance gate (lean-instance-gate six fields, short)

| L | structure above | theorem used as stated | missing components |
|:--|:--|:--|:--|
| L1 | ordered ring ℤ, divisibility | `Int.le_of_dvd`, `dvd_sub`, `pow_le_pow_left₀`, `sq_abs` | none |
| L2 | ℕ, `ZMod r` | `Nat.le_of_dvd`, `Nat.sq_sub_sq`; `orderOf_neg_one`, `ZMod.ringChar_zmod_n` | none |
| L3 | `ZMod p` field, `WeierstrassCurve`, `VariableChange` action | `pow_gcd_eq_one`, `ZMod.pow_card_sub_one_eq_one`, `WeierstrassCurve.variableChange_a₁…a₆`, `VariableChange.ext`, `mul_self_eq_one_iff` | none |
| L4 | `Field`, `Monoid`, `Algebra (ZMod p) K` | `pow_sub_one_mul`, `ZMod.pow_card`, `Nat.mul_div_assoc`, `Nat.Coprime.dvd_of_dvd_mul_left`, `pow_mul` | `sq_sub_one_div_eq` (a ℕ identity) |
| L5 | `CommGroup`, `IsCyclic`, `powMonoidHom`, `Subgroup` | `pow_card_eq_one'`, `Nat.gcd_eq_gcd_ab`, `IsCyclic.exists_generator`, `MonoidHom.map_zpowers`, `Nat.card_zpowers`, `orderOf_pow_of_dvd`, `Subgroup.eq_of_le_of_card_ge`, `pow_eq_pow_iff_modEq`, `Nat.modEq_and_modEq_iff_modEq_mul` | none |

Each proof is the cited theorems applied to the instance equalities; no limit
raised, no `native_decide`, no definition opened (`jZeroCurve`, `negChange` are
anonymous-constructor values of Mathlib structures).

## Axioms

All 17 reported theorems: `[propext, Classical.choice, Quot.sound]` or a subset
(`sq_sub_one_div_eq`: `[propext]`; `sixth_root_pow_eq_one`: `[propext, Quot.sound]`).
Gate: PASS (see receipts).
