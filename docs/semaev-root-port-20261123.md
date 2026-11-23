# Semaev root chain: port of KeyAIGit/ecdlp-lean-verification PR #347

2026-11-23. Source: [KeyAIGit/ecdlp-lean-verification#347](https://github.com/KeyAIGit/ecdlp-lean-verification/pull/347)
at head `0a47cd62f43d` (Lean v4.31, Mathlib v4.31.0). Target: this repository's pin
(Lean v4.35.0, Mathlib `cfc55fc`). Receipt: [`receipts/SemaevRootPort20261123/`](receipts/SemaevRootPort20261123/).
Trust manifest: [`../tools/lean/trusted-native.txt`](../tools/lean/trusted-native.txt).

## What was ported

Every module of the source PR, plus its import closure inside the source
repository: 52 modules, about 10.5k lines. Each file starts with a
`-- Ported from …` line that names its source path and commit.

| floor | modules | contents |
|:--|:--|:--|
| `CryptoLean.Semaev` (generic) | `S3Laws` | chord, tangent, two-root and iff laws of the existing `S3`, which is now stated over any `CommRing` |
| `CryptoLean.Semaev.Projective` (generic) | `FixedDegreeResultant`, `SylvesterConvention`, `RecursiveFamily`, `RecursiveWitness`, `GuardSystem`, `ChartSystem`, `InfinityStrata`, `LeftFoldAffine` | fixed-degree projective resultants; the left-fold recursive projective Semaev family `frozenC k b s` (`C_(s+2)`) for `y² = x³ + b`; its chain, guarded-system and chart-cover semantics; the affine left fold `C R b s` and `S17At b x X` |
| `CryptoLean.Secp256k1` (instance, `b = 7`) | 43 modules, aggregator `CryptoLean.Secp256k1` | the curve over `ZMod p`, Pratt primality of `p` and `n`, `#E(F_p) = n`, torsion, the Kummer fibre over the algebraic closure, the M16 factor base and liftable census, the Frobenius split, direct point semantics, the root bridge and root lower bound, solver gate, six-width no-go results |

## Headline results

| claim | Lean | kind |
|:--|:--|:--|
| The left-fold `S17` representative is the specialization of the projective family at stage 14 | `CryptoLean.Semaev.LeftFoldAffine.S17At_eq_frozenSpecialize` | law (any field, any `b`) |
| Over an algebraically closed field, a member of the family vanishes iff there is a full chain of projective witnesses | `CryptoLean.Semaev.FrozenProjective.specializeOver_frozenC_eq_zero_iff_projectiveChain` | law |
| Stage 14 vanishes iff there is a chart-polynomial cover, after any injective coefficient map | `CryptoLean.Semaev.FrozenProjective.frozenRecS17_iff_chartPolynomialCover_over` | law |
| **Root bridge:** the solutions of the 16-row direct System (4) correspond exactly to factor-base roots of `S17At 7 · X` | `CryptoLean.Secp256k1.M16DirectSystemRootBridge.directSolEquivReduced` (an `Equiv`) and `S17At_eq_zero_iff_chartPolynomialCover_over` | instance obligation |
| **Point semantics:** `S17At 7 x X = 0` iff there are points over the `x i` and a point over `X` whose sum is zero, in `E(F̄_p)` | `CryptoLean.Secp256k1.M16DirectPointSemantics.S17At_eq_zero_iff_exists_point_relation` | endpoint |
| **Root lower bound:** for each liftable anchor `A`, the target `R = −2A` is nonzero and has ≥ 564522⁷ direct roots (≥ 283527⁷ liftable roots), which exceeds the budget `B` | `CryptoLean.Secp256k1.M16CancellationRootLowerBound.cancellation_pair_root_lower_bounds`, `exists_target_budget_lt_directRoot_card` | endpoint |

## Instance gate (lean-instance-gate)

1. **Structure above.** Mathlib's `Polynomial.resultant`, `MvPolynomial`,
   `IsAlgClosed`, and `WeierstrassCurve.Affine.Point` with its
   `AddCommGroup`; crypto-lean's `CryptoLean.Semaev.S3`.
2. **Theorem used as stated.** Mathlib's resultant common-root theorem over an
   algebraically closed field (behind `HasCommonProjectiveRoot`), and the point
   group law. The new laws, the recursive-family laws, go in the generic
   `Semaev.Projective` floor.
3. **The object as an instance.** secp256k1 is `y² = x³ + 7` over `ZMod p`. It
   is the `b = 7`, `k = ZMod p`, `K = AlgebraicClosure (ZMod p)` instance of
   the projective family.
4. **Assembly probe.** The secp256k1 bridge theorem is the generic
   `frozenRecS17_iff_chartPolynomialCover_over` at `b = 7`. Its proof is that
   application followed by `map_ofNat`.
5. **Missing components.** None was re-derived. The port added
   `S3Laws` (the source's `S₃` laws, moved onto the existing `S3`) and four
   explicit `Fintype` equivalences (see "Deviations").
6. **Inheritance.** `S₃` uses crypto-lean's `S3` (`rfl` via `f3_eq_S3`). The
   point group comes from Mathlib. Finiteness of the points is the source's
   `instFinitePoint` (upstream candidate, below).

## Fidelity (formal vs claim)

| claim as written | Lean theorem | weaker or different in Lean | receipt |
|:--|:--|:--|:--|
| "solutions of System (4) are exactly the factor-base roots of S17" | `directSolEquivReduced` | none: an explicit bijection over `F_p` | gate PASS (trusted) |
| "S17 vanishes exactly on point relations" | `S17At_eq_zero_iff_exists_point_relation` | points are in `E(F̄_p)`, not `E(F_p)`; the base-field split is `M16FrobeniusPointSplit` / `M16PartitionedPointSemantics` | gate PASS (trusted) |
| "every all-roots enumerator needs more than B outputs on some target" | `exists_target_budget_lt_directRoot_card` | an **output-count** bound: it is not a PFPO, runtime or rank bound, and the relations are degenerate (cancelling pairs) | gate PASS (trusted) |
| "B is the uncalibrated 2^128 desk ceiling" | `M16SolverGate.maxRelationTermBudget` | B is a literal; its maximality as `max{t : μ₀t < 2^128}` is checked by `native_decide` window lemmas, not derived | gate PASS (trusted) |
| generic family "for y² = x³ + b" | `RecursiveFamily.frozenC` etc. | `a = 0` is fixed | gate PASS |

All results are kernel-checked from `propext`, `Classical.choice` and `Quot.sound`,
except where a theorem's line in `tools/lean/trusted-native.txt` says otherwise.
246 secp256k1 theorems depend on `native_decide` certificates, almost all
through the Pratt certificates behind `Fact p.Prime`. Two generic theorems,
`card_separatedInfinityMask` (987) and `card_interiorSeparatedInfinityMask`
(377), also use it; nothing downstream uses them.

## Deviations from the source

- **b is a parameter.** The source fixed `y² = x³ + 7` in the generic family
  (literal `28 = 4·7`, `f3 0 7`). Here every definition in
  `Semaev.Projective` takes `b`, and the secp256k1 modules pass `7`. Statements
  are otherwise unchanged.
- **One S₃.** The source's `Ecdlp.Semaev.S₃` duplicated `CryptoLean.Semaev.S3`.
  Its laws are now stated over `S3` in `S3Laws`, and `S3` is widened from a
  field to a commutative ring.
- **Mathlib-pin fixes.**
  - `import Mathlib.Algebra.MvPolynomial.CommRing` is now explicit, because it
    is no longer transitive.
  - `deriving Fintype` fails at `cfc55fc` for every inductive, so four
    instances are written as `Fintype.ofEquiv`. Three cardinality theorems that
    used `native_decide` now have kernel proofs: `card_guardVar_fourteen`,
    `card_guarded_equations_fourteen`, `card_chartEquation`. A fourth,
    `card_infinityMask`, also has a kernel proof now.
  - One `simp` that no longer unfolds `Finset.mem_filter` (`GenericGroupBound`).
- **Namespaces.** `Ecdlp.*` became `CryptoLean.Secp256k1.*`, and the generic
  namespaces became `CryptoLean.Semaev.{ProjectiveResultant, TaskSylvester,
  FrozenProjective, LeftFoldAffine}`.

## Source review findings carried over

The note `SECP256K1_M16_ALLROOTS_COST_BRACKET_2026_08_10.md` was not ported.
Its §12 still lists the `S17` representation and the two-sided bridge as
missing, but this chain proves both. Its audited base `6cde2788…` is not in
the source repository's history.

## Upstream candidates

- `CryptoLean.Secp256k1.AffinePointFinite.instFinitePoint`: `Finite` points of
  any Weierstrass curve over a finite ring. This is generic and belongs in
  `CryptoLean.Curve` or Mathlib.
- `CryptoLean.Secp256k1.GenericGroupBound` and `DlogCompleteness`: generic
  group statements that are stated in the secp256k1 floor.
