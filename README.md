# CryptoLean

A shared Lean 4 library for
[aburan28/crypto](https://github.com/aburan28/crypto),
[aburan28/cryptanalysis](https://github.com/aburan28/cryptanalysis) and
[aburan28/crypto-autoresearcher](https://github.com/aburan28/crypto-autoresearcher):
faithful definitions of the objects our proofs are about, and the proof gate
that checks them. The design and migration plan are in [docs/DESIGN.md](docs/DESIGN.md).

**Pinned:** Lean `v4.35.0`, Mathlib `cfc55fc` (2026-10-15). Every consumer
must build on the same toolchain (Lake requires it).

## Layers

| library | imports | contents |
|:--|:--|:--|
| `CryptoLeanCore` | Std only | `iterate` and return times; the N83 state-count bounds (`pairStates`, `squareStates`, `requestedEntries`, with proofs that the source files' two spellings agree); `GF(2)[t]` on `Nat` bit patterns (kernel-reducible, no `native_decide` needed); SplitMix64 |
| `CryptoLean` | Mathlib | short Weierstrass models and their generic, quartic and sextic twists; torsion fixing; cyclic and finite-field subfield twist tests; conductor arithmetic; Semaev's S₃ and its roots `x(R±F)` |
| `CryptoLean.Bridge` | both | proofs that a `Core` computation means the Mathlib object (so far: `iterate` equals `f^[n]`, `Returns` iff `Function.IsPeriodicPt`) |

`CryptoLean` contains promoted consumer proofs and shared generic laws.
Promoted files name their source; new laws document their consumer and
mathematical reference.

`CryptoLean.Group.GenericDLog` and `CryptoLean.Curve.SubgroupDLog` bound
adaptive generic discrete-log success by `(q + 3)(q + 2)/(2r) + 1/r`
for `q` queries and prime subgroup order `r`. At fixed order, every query
budget has the same attainable success on either curve. These modules
formalize the affine collision argument from [Shoup](https://www.shoup.net/papers/dlbounds1.pdf).

`CryptoLean.Curve.ConductorGapQueryBound` combines the Frobenius
discriminant identity and a cofactor cap with the generic query bound.
`CryptoLean.Curve.DLogSolverTransport` preserves exact success for
coordinate-aware solvers given additive maps with the dual-degree identity
and degree coprime to `r`. The maps are inputs to the theorem, and the
running-time overhead depends on the cost of evaluating them.

`CryptoLean.Curve.PrimeFieldBarrier` extends the generic collision bound
to explicitly supplied polynomial zero tests over the scalar field. Its
randomized version uses the expected total degree over seeds independent
of the challenge. The prime-field estimate also takes the Hasse inequality
and a cofactor cap as hypotheses.

`CryptoLean.Polynomial.EllipticMaps` supplies the cleared doubling quartic,
degree-two Vélu curve residual and its kernel-root/affine specializations.
They concern semantic rings and fields. Native source binding, rational-root
completeness, point-group semantics and complete algorithmic cost remain
consumer obligations.

`CryptoLean.Polynomial.InterpolationKernels` separates actual degree-bounded
evaluation kernels of clean colored prefixes and counts their finite range
as b^t when t is within the u-degree cap. It also represents their union
exactly by products of evaluation forms, keeping nonzero extraction explicit.
It supplies no witness-search algorithm. The prospective inheritance plans,
actual prime-field coordinate assembly and build receipts are linked from
`docs/interpolation-kernels-20261115.md`. Its recorded gate audited 167 theorems,
0 failures and 0 trusted-native exceptions. The gate dependency recovery and
both earlier failed receipts are retained beside the source pins.

`CryptoLean.Curve.CenteredCompletion` reads exact two-point completion from
Mathlib's infinity-aware x representative after translation. The distinct-record
and half-target hypotheses are explicit. Its generic/prime-field assembly,
prospective plan and full audit169/0/0 are linked from
`docs/centered-completion-20261115.md`. The pencil interpretation, explicit
batch costs and fixed-family yield bound are separately labelled hand analysis;
implicit anchor lifting remains open. [pcc:unverified]

`CryptoLean.Group.PartiteCoverage` counts actual zero-sum tuples in disjoint
random lists over any finite additive commutative group. It derives exact
single/pair event counts and both moments, then the integer coverage bound
equivalent to `Pr[Z>0] >= L/(r+L-1)`. It proves existence coverage, not a fast
relation selector. Source/axiom receipts and the finite model are in
`docs/partite-coverage-20261115.md`.

`CryptoLean.Curve.LineIncidence` reuses Mathlib's Weierstrass equation and
addition polynomial to bound secant fibres. A finite family of s prescribed
slopes has at most 2s distinct-abscissa affine partners for any known curve
point. It is a geometric count; probabilistic sampling and algorithm costs
remain consumer obligations. See `docs/line-incidence-20261115.md`.

`CryptoLean.Group.SubsetFourier` assembles finite-subset Parseval and actual
additive-triple counts from existing character orthogonality. An explicit
nontrivial-character bound M yields the triple-count deviation M*|S|. The
elliptic analytic input and any sampling interpretation remain separate.
Source, inheritance and audit receipts are in `docs/subset-fourier-20261115.md`.

## Using it

In the consumer's `lakefile.toml`:

```toml
[[require]]
name = "CryptoLean"
git = "https://github.com/aburan28/crypto-lean"
rev = "v0.1.0"
```

Then `lake update CryptoLean`, commit `lake-manifest.json`, and set
`lean-toolchain` to this repository's.

## Proof gate

`tools/proof-gate.sh` builds every Lean target of the repository it is run in
and audits each theorem's transitive axioms with `tools/AuditAxioms.lean`.
Only `propext`, `Classical.choice` and `Quot.sound` pass. `sorryAx`, an
unlisted `native_decide` and user axioms fail. So does a target with no
theorems. Consumers run the pinned copy from their repository root:

```sh
.lake/packages/CryptoLean/tools/proof-gate.sh
```

For a Lake project the gate also builds each tracked proof source explicitly,
using its source-path target, before auditing the built modules. An unregistered
auxiliary source compiles into a private directory and is audited with the project,
without changing frozen Lake configurations. A source build failure fails the gate.
Nested projects are checked separately. Lake
configuration, the gate auditor and deliberate gate fixtures under `tools/lean`
or `tools/selftest` are outside the proof inventory. The receipt's `sources.log`
records that inventory. Untracked files are not covered by repository discovery.

A deliberate `native_decide` goes in the consumer's
`tools/lean/trusted-native.txt` with its reason, and is reported as `TRUST`.
`tools/selftest/run.sh` checks the gate itself: every fixture must pass or
fail *for the expected reason*, so a broken audit cannot pass the self-test.
Project controls include unconfigured true and false proofs and configured positive and
negative modules, independently of the default root's successful build.

Passing the gate shows that a theorem is proved from the standard foundations.
It does not show that the theorem is the claim a report makes. That still
needs review.

## Not yet in v0.1.0

- the `Bridge` theorem relating `GF2Poly.mod` to `Polynomial (ZMod 2)`
  reduction;
- the group-level `PointIsogeny` and the generic-group model on Mathlib `Group`;
- autoresearcher's Semaev symmetrization and fall-degree material;
- the `@[report_theorem]` attribute (design phase 4).
