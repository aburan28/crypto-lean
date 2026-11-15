# Quadratic norm transport: local proof receipt

Source commit: f74b0e8bd3815fdf2adae5b180431fc94d2be107.
Lean4.35.0; Mathlibcfc55fc58714a59dc06e6e79edc6d1d95140d3c2.

The new module inherits Conductor.quadraticNorm, proves a generic reciprocal-root
factorization/divisibility law, and specializes its positivity, rotation,
positive-multiple and sector bounds to the Eisenstein form. It does not
formalize abelian varieties or prove a cryptographic speedup.

Local command:

```sh
bash tools/proof-gate.sh --out /workspace/scratch/shared-norm-proof-gate .
```

The canonical gate audited115theorems, with0failing and0trusted native
exceptions. Included are seven new generic norm lemmas. `sources.sha256`,
`build.log`, `audit.log` and `status` preserve the exact source/toolchain
bindings and result. These are local producer receipts, not independently
signed PCC standing. [pcc:unverified]

The P-256 consumer applies these laws to its fixed n/lambda and keeps its
geometric polarization formula as an explicit hypothesis. Its new native
map candidate has not been numerically qualified. No timing or unknown-scalar
recovery is inferred from this library change. [pcc:unverified]
