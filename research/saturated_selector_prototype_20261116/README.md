# Certifying saturation prototype — unexecuted

This is a complete SOURCE candidate for the stages of an interval-factor-base
index-calculus attempt: catalog construction, mixed-target decomposition,
factor-base cancellation and a final scalar check. It has **not run under
Sage**, has no measured yield or runtime, and does not establish a classical
subexponential ECDLP algorithm. Capped failure is an allowed outcome.

The decomposition routine receives the point target and fixed catalog,
without its alpha/beta scalar labels. It compares ordinary homogenized S3
constraints with modular denominator saturation. Saturation returns explicit
polynomial lift witnesses. A finite Macaulay shift family is grouped by
projective multidegree; exact LLL transformations and integer L1 bounds are
checked before homogeneous identities are promoted. A checked lexicographic
projection eliminates ratio coordinates. A bounded exact monomial staircase
admits finite leaf root recovery, followed by original point/sign checks.

This Macaulay control is not Ryan's optimal D-Groebner shift selector.
Neither a short row nor a successful toy case proves independent equations,
useful random-target yield, or a growing-system complexity bound.

## Files

- `metadata.py`: dependency-free caps and monomial-count admission.
- `launch.py`: fresh-output, process-group timeout and resource-limit wrapper.
- `worker.py`: Sage candidate, including all end-to-end stages and certificates.
- `verify.py`: separate exact catalog/relation/scalar replay without a lattice.
- `pilot.py`: paired, frozen known-answer controls and separate outcome axes.
- `fixtures/`: copied public toy input; no curve case was evaluated here.
- `Dockerfile`: digest-pinned runtime recipe; no image was built here.

Static verification consists of source parsing, launcher help and six generic
resource/count controls. These tests do not import Sage or perform curve/LLL
calculations. Prior Lean271/0/0 evidence covers the existing mathematical
components; it does not verify this Python/Sage implementation.

## Future execution contract

The exact protocol is `pilot-protocol.json`. It is a research protocol, NOT
an `isolab.eks.request/v1` launch request. Before any job, complete the
maintained IsoLab image/source/permission, capacity, remaining-budget,
publication and S3 receipt checks. The registry digest was resolved read-only;
the runtime image has not been pulled, built or qualified. Use EKS Spot under
the standing backend rule; do not run a numerical substitute locally.

Within an admitted image the intended argv is:

```
sage --python /opt/selector/pilot.py --output /work/results
```

The controller has a360-second bound; two workers each have120-second wall
and90-second CPU limits, with one8GiB container requested and limited. The
future Job has a600-second total deadline and zero automatic retries. The
proposed total ceiling is USD2 including image build, idle/queue, storage,
transfer and failed attempts. It is not a cost estimate or a budget grant.
No job may start while the shared remaining daily/monthly balance is unknown.

Worker artifacts share one output cap, with another per-log cap for stdout
and stderr. RLIMIT_AS is per process: the EKS container memory limit must
bound the whole tree. A timeout, output cap, positive-dimensional projection
or missing dependency is a recorded failure, not an emptiness certificate.
Every worker output directory must be fresh. Preserve all raw stage evidence.

For the public toy, input labels are a fixed known-answer control, not uniform
samples for estimating yield. An identity/catalog/two-sum scalar recovery
does not establish that the saturation path worked. The pilot records
certificate consistency, actual saturation-path usage and scalar replay as
separate outcomes. The expected scalar is outside the worker input.

The standard free-label probability argument additionally requires its
uniform and label-free hypotheses. It is not asserted for wall-time-censored
pilot runs. Scalar log fields use fixed widths to avoid direct label-length
effects on the shared byte budget.

## Sources

Ryan2025, UCSD thesis chapter3; cuso commit
`fb2747d2105a8e48499bf10a3a717cf80c14d079` (API/default-L1 context only,
no code copied); Sage official saturation/lift/LLL/Groebner documentation;
CHHS2016 and CHHS2021 capacity-theory primary papers. The public toy is
David Ahlqvist2022, U.U.D.M.2022:49, pp15--16/table1, reproducing Paar--Pelzl
Example9.5. Full URLs/hashes/scopes are indexed in the publication notes.
KB tools unavailable; bounded primary/owner/Mathlib fallback, no novelty claim.
