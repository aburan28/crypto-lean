# F: first generic law and inherited product assembly

This is a new proof unit, not a replay of the old Bool/Init proof. The
six-field instance/fidelity design is PROOF_MAP.md; actual law source is
CryptoLean/Group/UniqueDouble.lean, with inherited product obligations and
controls in UniqueDoubleExamples.lean. Shared library laws precede study
consumer migration. No geometric isogeny, Jacobian realization or solver
advantage follows from a point-group endpoint alone. [pcc:unverified]

Question/prediction: the stated AddMonoid law should compile from map_add,
map_zero and injection, without a nonzero hypothesis in the basic theorem.
The C4 x C2 x C2 endpoint should instantiate it through the existing ZMod and
product groups. Zero-map and elementary-two-group swap controls should show
that injection and the represented-point witness cannot just be omitted.
A degenerate zero-point endpoint should also compile. [pcc:unverified]

First-call plan: once official compatible dependencies exist, direct pinned
Lean with explicit-j1 builds the generic module first and its actual product
assembly second, warnings as errors, then runs the unchanged canonical
AuditAxioms.lean on both modules. No Lake/Mathlib source build. Each phase
has two-GiB virtual-address/120second/one-worker bounds and default logical
limits. Actual Lean/runtime bytes and all source/caller/auditor/dependency
pins are locked and compared before/after. This does not claim that a focused
audit is the whole-repository proof gate or a signed PCC verdict.
[pcc:unverified]

Observables: complete argv/streams/exits/guards, actual axiom printout and
canonical auditor theorem inventory. Success requires both compiles and
all-audited-standard-axioms exit0 with matching guards; failure retains the
first complete record before a separately published repair. No sorry, admit,
custom axiom, native_decide or logical resource override. Fresh output
/dev/shm/law34-proofF and temporary /dev/shm/law34-proofF-tmp; full binary
outputs remain whole with custody stated. Source and full readback precede
the first call. Existing whole-project CI/gates must still pass before merge.
[pcc:unverified]

Fidelity table: AddMonoid/zero/addition/map laws are inherited; Mixed and
Elementary are existing product/ZMod instances; finite contracts reduce in
the kernel; F is an arbitrary AddMonoidHom and injection an explicit
hypothesis. Neither conclusion F(p)=p nor its nonzero obstruction is assumed.
The old Bool representation and general geometric classification remain
separate bridges. This probe earns only the instances actually compiled.
[pcc:unverified]
