# Cyclic-group and transport foundations

Lean 4.35.0; Mathlib cfc55fc58714a59dc06e6e79edc6d1d95140d3c2.
These reusable modules strengthen the earlier conditional retrospective proofs.
They establish algebraic facts, with the hypotheses below; they establish no
new cryptanalytic speedup, security reduction, map construction or machine-code
refinement. Independent semantic review is recorded in the consuming study.

| Module | Guarantee | Required hypotheses |
| --- | --- | --- |
| `CryptoLean.Group.CyclicEncoding` | `encode` maps a residue to its integer multiple of an actual point; exact-order injectivity, range equal to the generated subgroup; `walkPoint_eq_encode` connects `a.val • P + b.val • Q` to the scalar invariant | Additive commutative group; `n • P = 0`; exact order `addOrderOf P = n` for injectivity; nonzero modulus for `val` |
| `CryptoLean.Group.RhoCollision` | `collision_recover`, `negated_collision_recover` derive the two recovery formulas directly from equality/negated equality of actual walk points | Prime order of P; target Q is the canonical encoding of x; respective difference/sum denominator nonzero |
| `CryptoLean.Group.CoprimeTransport` | Explicit coefficient `Nat.gcdB (Nat.card S) d` recovers P from `back (f P)`; injectivity and both directions of the DLP equivalence follow | Finite subgroup S; degree coprime to its cardinality; supplied additive maps satisfy the reverse-composition identity on S |
| `CryptoLean.Group.FoundationControls` | Checked counterexamples around exact order, composite scalars, zero denominators and noncoprime multiplication | Concrete ZMod 6 and ZMod 7 examples; ordinary kernel-checked proofs |

The generic additive groups include Mathlib elliptic-curve point groups.
Constructing a particular curve, certifying its point order, proving the
reverse-map identity and connecting a C implementation remain application
obligations. An assumed identity is always visible in the theorem type.

Reproduce from the repository root:

```sh
lake build
lake build +CryptoLean.Group.FoundationControls
lake env lean --run tools/AuditAxioms.lean CryptoLean.Group.CyclicEncoding CryptoLean.Group.RhoCollision CryptoLean.Group.CoprimeTransport CryptoLean.Group.FoundationControls
# Complete tracked-source repository gate, also used by consumers:
tools/proof-gate.sh --out /tmp/crypto-lean-foundation-gate .
```

The scoped audit covers 19 new theorem declarations, including five controls.
This count is machine coverage, not independent semantic approval. Standard
Lean axioms only; no compiler-trust exceptions. Pinned dependency binaries
remain within Lean/Lake's normal trust boundary; no independent binary
rechecker is installed.
