# Coefficient-first endpoint selector — source only

This UNEXECUTED library searches one declared modular row family p*Z^20+Z*F.
It is not an ECDLP solver. The parent must certify p is an odd prime, preserve
inputs/source custody and enforce the existing backend/admission/budget and
whole-process/output limits. No numerical case or performance result exists.

The first S3 endpoint has coefficient1 at x²y²V² and2*tau at x²UV. Shortness
therefore puts the scalar and offset in two exact integer windows. Enumerate
the nonzero first coefficient c1 and second c2, derive tau=c2/(2*c1) modulo p,
then center all20 combined coefficients. Each candidate row has the minimum
positive weighted L1 for its scalar/offset pair. The formal RankOneSelector
owner proves existence-search soundness/completeness under these identities,
not formal verification of this Python implementation.

This does not enumerate every integer lift of a short row. It finds a no-worse
centered representative for every feasible scalar/offset pair. It does not
prove that certificates exist or isolate useful roots. A completed empty
search certifies absence only in this rank-one model. Caps or interrupted
runs return incomplete and cannot certify absence.

Call select_first_endpoint from an admitted parent, reuse ONE Budget over
all models/profiles, and supply an event sink that retains every pair/row and
raises IncompleteSearch on a shared output cap. Reserve terminal metadata
space in the parent. All scalar/coefficient/offset records survive even if
polynomials coincide. Accepted rows carry exact p-row witnesses. The library
has no standalone launch command or implicit authorization to run research.
No Sage/curve/LLL/numerical/native, paid or qualification run occurred here.
