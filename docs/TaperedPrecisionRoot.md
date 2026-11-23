# Finite precision at a contraction root

`CryptoLeanCore.TaperedPrecisionRoot` extends the existing exact Nat source
expression without changing `TaperedPrecision` or its conditional34 law.
All observations below are producer records, PCC unsigned. [pcc:unverified]

For natural p,M,u,i, the new finite law is

```
p <= M, 32*u <= M, i < u
  => childPrecision p M u (2*u) i * u <= 35*M*2^(2*u-i).
```

The source root length/array inequality implies the margin32u<=M, so
`root_precision_of_array` accepts that inequality instead. No inherited-path
or asymptotic absorption premise is hidden. The result is only at a=2u.

| Declaration | Exact contract |
| --- | --- |
| `root_evaluation_envelope` | 0<u implies16u(2u+1)<=21*2^(u+1) |
| `root_four_scale` | 0<u implies4u<=2^(u+1) |
| `root_array_margin` | 2^(2u)*64^(4u)<=M implies32u<=M |
| `root_precision_mul_le` | p<=M,32u<=M,i<u imply the35 bound |
| `root_precision_of_array` | p<=M,i<u and array guard imply the35 bound |

Put D=2^(2u-i). The active valuation gives D>=2^(u+1).
Multiplying the three source precision terms by4u bounds them by MD,
97MD and42MD. The last uses the polynomial/power law above; the middle
uses floor-division remainder and32u<=M. Their sum140MD gives35 after
cancellation. The array guard is2^(26u)<=M and dominates32u.

The consumer proves the exact normalized family
`2*childPrecision(E+1,2E,2,4,1)=546E+2`; it exceeds the34 envelope544E.
For the weaker margin domain take E>=32; for the full array guard take
E>=2^51. This does not refute the old34 law, whose extra absorption premises
fail here, or the paper's asymptotic Big-O statement. [pcc:unverified]

Focused Lean4.35.0 compilation, all five explicit axiom queries and unchanged
repository gate pass. A separate consumer has seven controls and12 total
queries; official `leanchecker --fresh RootControls` replays the imported
and defined environment with exit0. Foundations are propext/Quot.sound;
the consumer34-family proof also uses Classical.choice; three numerical
controls use none. No native_decide, custom axiom, hole or limit override.
The fresh checker is the official kernel, not an external verifier. Retained
receipts identify the exact sources and commands. [pcc:unverified]

Written source review and a separate native BigUint program are in the
consumer study `isogeny-labs/crypto:research/hashed_ecdl_root_precision_20261123`,
PR4996, formal PCC759751 and native PCC4b3d64, both unsigned. Earlier failed
proof/import/resource attempts remain in that study's local checkpoint and
publication records. Its current-main PCC ledger prefix conflict is open.
No complete-library Mathlib build, signed CI or end-to-end cost theorem is
claimed by these focused checks. [pcc:unverified]

Actual checked Rust arithmetic, graph construction, source histories, later
depths and total bit cost remain consumer obligations. Current64-bit usize
Setup has root_u0; the huge translated witness is expressly unbounded scalar
arithmetic, not production admission. No dependency/toolchain/gate is changed.
