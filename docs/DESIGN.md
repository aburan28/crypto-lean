# Design: a shared Lean library for crypto, cryptanalysis and crypto-autoresearcher

**Status.** Proposal, 2026-10-16. Nothing here is built yet.
**Builds on.** The repository-wide proof gate
([aburan28/crypto#1936](https://github.com/aburan28/crypto/pull/1936),
[aburan28/cryptanalysis#932](https://github.com/aburan28/cryptanalysis/pull/932)).

## 1. Why

The proof gate shows that each theorem is proved from Lean's standard axioms.
It cannot show that the theorem is *about the right object*. The inventory
below shows that this is where the real risk is.

## 2. What exists today (measured 2026-10-16)

| repo | Lean code | toolchain | Mathlib |
|:--|:--|:--|:--|
| crypto | 42 files, 2,882 lines, 13 Lake projects + 13 standalone files, 314 theorems | v4.34.1 | `d13f23b` (4 projects); 9 projects use no Mathlib |
| crypto-autoresearcher | `formal/` workspace: `Semaev/`, `FallDegree/`, 8 target specs | v4.35.0-rc1 | `7fa2273` |
| cryptanalysis | none | none | none |

Findings:

1. **Hand-rolled algebra with no laws.** Nine crypto projects avoid Mathlib
   and define their own `GroupOps`, `MonoidOps`, `Hom`, `Isogeny extends Hom`,
   `CommMul`, `AddOps`, `iter`/`Ret`. A structure that holds operations but no
   axioms is not a group. A theorem about such an `Isogeny` does not by itself
   say anything about isogenies of elliptic curves. Each study has to argue
   the correspondence in prose, and nothing checks that argument.
2. **Duplication inside crypto.** `stateBound` is defined 8 times across the
   N83 capacity files, in two different forms (`83·C(k,2)+42k` and `83·k²`).
   `requestedEntries`, `iter` and `Ret` are each defined twice.
3. **Duplication across repos.** Semaev's S₃ appears in
   `papers/rootfinding-decomposition/lean/S3Roots.lean` (crypto) and in
   `formal/CryptoResearch/Semaev/` (autoresearcher). Each repo wrote its own
   axiom audit: crypto's audits by module, autoresearcher's by namespace.
4. **Incompatible pins.** Lake builds every package on one toolchain, so as
   pinned today neither repo could import the other's Lean code.
5. **Good material to promote.** `WeakCurveProperties` already builds on
   Mathlib's `WeierstrassCurve`: short models, generic, quartic and sextic
   twists, torsion fixing, cyclic-twist tests and finite-field subfield
   twists. That is the right base layer.

## 3. Decisions

### 3.1 One package in its own repository

Create **`aburan28/crypto-lean`**, providing the Lake package `CryptoLean`.
Each consumer adds it as a git dependency, pinned to an exact commit by its
committed `lake-manifest.json`:

```toml
[[require]]
name = "CryptoLean"
git = "https://github.com/aburan28/crypto-lean"
rev = "v0.1.0"        # the manifest pins the commit
```

Why a separate repository rather than a directory in crypto:

- three consumers, one source;
- it removes the `tools/lean/` copy that cryptanalysis#932 had to make;
- the library gets its own CI and version tags.

### 3.2 One toolchain, moved in lockstep

- Pin **Lean v4.35.0** and the Mathlib commit that declares it. The library's
  `lean-toolchain` is copied from Mathlib, never written by hand (this is
  already how autoresearcher's `setup.sh` works).
- A bump is one PR in crypto-lean, tagged, followed by a bump PR in each
  consumer. crypto-lean CI builds the consumers' Lean targets against the
  candidate tag before it is cut, so breakage is found upstream.
- Frozen studies keep their own pinned toolchain and stay buildable with it.
  The proof gate already handles per-target toolchains. Only new or migrated
  work moves to the shared pin.

### 3.3 Three layers

| layer | imports | contents | used for |
|:--|:--|:--|:--|
| `CryptoLean.Core` | Std only | `Nat`/`UInt64` bit lemmas, GF(2)[t] polynomials encoded as `Nat` (`polyMod`, `polyMul`), `splitmix64`, capacity-bound helpers (`stateBound` family, one definition each, named by form), `Function.iterate` lemmas instead of private `iter` | fast `decide` certificates and replays (N83 capacity, tree-split) with no Mathlib build cost |
| `CryptoLean` | Mathlib | short Weierstrass models and twists (promoted from `WeakCurveProperties`), the point group through Mathlib's `WeierstrassCurve.Affine.Point` (`AddCommGroup`), torsion and `mulBy`, endomorphism and conductor arithmetic, Semaev polynomials as `MvPolynomial` plus their symmetrization (merging both repos' versions), and the generic-group model as Mathlib `Group` plus an oracle | statements about the real objects |
| `CryptoLean.Bridge` | both | theorems that equate each `Core` computation with its Mathlib meaning, for example `polyMod` on `Nat` equals `Polynomial (ZMod 2)` reduction | lifting a fast `decide` result to a statement about the real object |

`Bridge` is the fidelity layer. A study can check data at `Core` speed and
still state its theorem about Mathlib objects, with the link proved rather
than asserted.

**Isogenies.** Mathlib has no isogenies of elliptic curves as morphisms of
varieties. `CryptoLean` will define `PointIsogeny` as a group homomorphism
between point groups, with its kernel, and its docstring will say it is that
group-level abstraction. Reports that use it must say so too. It never
replaces a statement about morphisms of curves.

### 3.4 One gate, shipped by the library

- Move `AuditAxioms.lean`, `proof-gate.sh`, the trust-manifest format and the
  self-test into crypto-lean. Consumers run the pinned copy from
  `.lake/packages/CryptoLean/tools/`, so all three repos run identical code.
- Merge the two audits. Module-based discovery (crypto's) finds everything a
  project built. Autoresearcher's per-target audit of one named theorem stays
  as a mode, because its worker needs it.

### 3.5 A machine-readable proof map (phase 4)

Add an attribute `@[report_theorem "research/<study>/REPORT.md#thm-3"]`. The
audit would then:

- list every tagged theorem with its axioms, which gives AGENTS.md's proof map
  automatically;
- fail when a tagged theorem is `TRUST` (a reported result may not rest on
  `native_decide`);
- fail when the report anchor does not exist.

The human fidelity review (does the statement match the report?) stays
required. The attribute makes it impossible to skip silently.

## 4. Migration plan

| phase | work | done when |
|:--|:--|:--|
| 0 | create crypto-lean: toolchain v4.35.0, Mathlib pin, `Core` (deduplicated `stateBound` family, `polyMod`, `splitmix64`, iterate lemmas), `CryptoLean` (`WeakCurveProperties` modules, S₃), gate, self-test, CI | `v0.1.0` tagged; gate and self-test green |
| 1 | crypto: new studies import `CryptoLean`; the local gate is replaced by the pinned one | next new Lean study builds against `v0.1.0` |
| 2 | re-prove, as **versioned additions**, the hand-rolled studies whose claims depend on missing laws, starting with `conductor_gap_cm_pairs` (`Isogeny extends Hom`) and `weak_subfield_hyperelliptic_decomposition` (`CommMul`, `AddOps`). Frozen files are not rewritten (AGENTS.md) | each new proof states the original claim about Mathlib objects |
| 3 | autoresearcher: `formal/` requires `CryptoLean`; shared Semaev and fall-degree material moves to the library; targets stay in autoresearcher | the `formal-workspace` CI gate is green on the shared pin |
| 4 | `@[report_theorem]` and the generated proof map, in all three repos | the audit prints the proof map and enforces the rules in 3.5 |
| — | cryptanalysis: its first Lean proof imports `CryptoLean` | the gate from #932 builds it |

## 5. Risks

- **Mathlib bumps break proofs.** Contained by the upstream consumer build
  (3.2), and by frozen studies keeping their own pins.
- **Lockstep toolchains.** Consumers cannot mix pins in one build. This is
  inherent to Lake and is why bumps are coordinated.
- **Build time.** The Mathlib layer needs Mathlib's cache (about 5 GB). `Core`
  stays Mathlib-free so certificate studies stay fast.
- **False comfort.** A library of faithful objects lowers the fidelity risk
  but does not remove it. Statements still need review against the report.

## 6. Decisions needed from the owner

1. Repository name and visibility: `aburan28/crypto-lean`, public like all
   three consumers?
2. Toolchain: Lean v4.35.0 with the current Mathlib master commit?
3. Phase 2 priority: is re-proving `conductor_gap_cm_pairs` against real point
   groups worth doing before new work?
