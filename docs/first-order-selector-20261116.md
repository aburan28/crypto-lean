# Coefficient-first selection in a one-generator modular block

16 November2026. Source59cc763 provides an exact mathematical search model
and an UNEXECUTED Python source candidate. The model decides existence of a
nonzero norm-short row in a declared family p*Z^N+Z*F(tau), using two
coefficient windows instead of LLL. This is one generator MODULO p; the full
integer lattice has rank N. It is not a complete ECDLP algorithm.
[pcc:unverified]

The [prospective plan](first-order-selector-20261116-plan.md),
[source](../research/coefficient_first_selector_20261116/selector.py),
[editable flow](first-order-selector-20261116/flow.dot),
[PDF](first-order-selector-20261116/report.pdf) and
[publication boundary](first-order-selector-20261116/PUBLICATION.md)
retain the exact family and missing useful-yield obligations.
[pcc:unverified]

## The exact search

Let p be an odd prime. Fix positive integer coordinate weights w_i and a
coefficient model F(tau) over Fp, with two declared coordinates satisfying

    F(tau)[i1]=1; F(tau)[i2]=s*(tau-q), s!=0.
    Lambda(tau)=p*Z^N+Z*F_lift(tau).
    L1(c)=sum_i |c_i| w_i.
    n1=floor((p-1)/w_i1); n2=floor((p-1)/w_i2).

The full p rows on ALL columns matter: this is not an arbitrary truncated
shift lattice. Any integer lift of the same Fp model gives the same family.
The prime is a caller-certified precondition in the Python library, not an
unchecked claim of primality by the implementation. [pcc:unverified]

The procedure is finite and explicit:

1. Enumerate the nonzero first coefficient in its signed window and the second
   coefficient in its signed window (equivalently their admissible residues).
2. Derive tau=q+c2/(s*c1) modulo p.
3. Replace each coefficient of c1*F(tau) by its centered residue.
4. Emit that centered row only when it is nonzero and its exact integer L1
   is below p. Retain the scalar/offset pair and the exact p-row witness.

There are at most(2n1+1)(2n2+1) residue pairs. In the implemented first-endpoint
bounds the windows lie strictly inside a half modulus, so the raw signed
loop has exactly2n1(2n2+1) planned pairs and preserves them all. No loop over
all p offsets or all p scalar multipliers is hidden. [pcc:unverified]

The first coordinate identifies the row's scalar modulo p. If that scalar
were zero, every coefficient would be divisible by p; positive weights would
make a nonzero row have L1 at least p. For a nonzero scalar, shortness bounds
the first two integer coefficients and their relation determines tau.
Thus every nonzero short row has its scalar/offset pair among the candidates.
[pcc:unverified]

For each pair, coefficientwise centered residues minimize every positive
weighted L1 in its congruence class. Therefore an existing short row supplies
a no-worse centered representative, and the anchor1 makes it nonzero. The
converse is immediate from the explicit p-row witness. The compiled theorem
selected_iff_integer_short states the resulting equivalence for the declared
integer row family. This is a complete existence search, NOT enumeration of
every integer lift of every short row. [pcc:unverified]

## Actual S3 coefficients and certificate meaning

For the first endpoint, use the original homogeneous polynomial

    F_tau=(x-y)^2*(U+tau V)^2
      -2*((x+y)*(xy+a)+2b)*(U+tau V)*V
      +((xy-a)^2-4b*(x+y))*V^2.

Its coefficient of x²y²V² is1, and that of x²UV is2tau. The code's two
weights are B^4 H² and B²H², so the windows above are determined exactly.
The last endpoint, with one abscissa fixed at q, instead has coefficients1
at x²U² and2(tau-q) at x²UV. These identities compile using nested
univariate coefficient extraction. The current Python implementation covers
the FIRST endpoint only. [pcc:unverified]

The expansion has20 distinct combined monomials. Their exponent map is
proved injective, and their full symbolic expansion equals S3's translated
endpoint. A static AST translator reads the Python coefficient dictionary
without importing or running it, checks the monomial order, rejects unsupported
operations and generates a generic-ring Lean equality. That proof compiles,
checking all20 source formulas against the formal model. It does not prove
the Python loop, budget or exception implementation correct.
[pcc:unverified]

The compiled finite-row certificate laws bound the absolute integer value
by the weighted L1 and preserve modular divisibility through the row witness.
At |x|,|y|<=B and |U|,|V|<=H, each monomial is bounded by its declared weight.
Thus a selected short row vanishes as an integer at every bounded modular
root of this endpoint. Original nonzero-denominator, point/sign and relation
checks are still needed by an ECDLP consumer. One vanishing polynomial need
not isolate roots or supply an independent useful equation.
[pcc:unverified]

## Why coefficient-first differs from uniform offset sampling

For coefficient windows A and B, every admissible offset belongs to

    { q+(s*c1)^(-1)*c2 : c1 in A, c1!=0, c2 in B }.

The generic field-image cardinal bound and finite-pool miss lower bound are
compiled. For Q iid uniform offsets, a hand union bound gives hit probability
at most Q*(2n1+1)*(2n2+1)/p. If Q,n1,n2=p^o(1), that is p^(-1+o(1)). This
is a scoped upper bound for this row model, not a global impossibility.
[pcc:unverified]

The direct selector enumerates the coefficient image instead of hoping a
uniform pool meets it. At H approximately sqrt(p)/B^kappa, fixed kappa>2,
the windows have sizes O(B^(2kappa-4)) and O(B^(2kappa-2)); the candidate
count is O(B^(4kappa-6)). With B=p^o(1) and fixed20 columns, this gives a
subexponential arithmetic/output bound for the DECLARED first-order search.
That is hand bit-complexity accounting, not a measured speed result or an
implementation qualification. [pcc:unverified]

Coefficient-selected offsets are nonuniform. The earlier uniform chart-pool
coverage estimate cannot be transferred to them. The missing intersection
is between certificate-compatible offsets and charts containing useful
original decompositions. No lower bound for that intersection, no global
chart cover and no useful random-target yield are proved here.
[pcc:unverified]

## Capped source and verification boundary

The Python source keeps one shared pair/certificate Budget across models.
It reserves the complete pair family before search and retains every visited
signed-coefficient/offset record, including equal polynomial values and
rejections. Every accepted row has an exact integer modulus-row witness.
All large mathematical integers are serialized as decimal strings.
[pcc:unverified]

A completed search reports complete_empty or complete_nonempty only for this
rank-one model. Preflight, output, certificate or external interruption caps
mean incomplete and never certify absence. The parent must retain events,
reserve terminal metadata space and apply process/memory/time limits. No
standalone research launch or implicit budget grant is included.
[pcc:unverified]

Local evidence:44 named generic laws; five actual symbolic declarations;
one AST-translated table equality; all actual named axiom dependencies
standard. Full all-tracked gate001 exits0:347 theorems,0 failures,0 trusted
native. Two Python files parse; neither selector nor field arithmetic was
executed. Raw failures and warning whitespace remain. No proof-limit, trust,
inventory or linter exception. [pcc:unverified]

This is a model-level sound/complete selector plus an unexecuted source
candidate. It has no measured speed, success panel, Sage/curve/LLL numerical,
native, paid or qualification run, independent signed verdict or evaluated
identity certificate. The existing live cost/reservation record, source-image
custody and caller/capacity admission remain missing for any future trial.
[pcc:unverified]

## Remaining end-to-end gap

An ECDLP algorithm must still obtain enough independent useful equations,
recover bounded original decompositions at charged cost, cancel their actual
factor-base provenance and verify the scalar. None follows from exact short-row
selection in one block. Higher-rank families need separate pivot/window and
cost arguments; arbitrary saturation families are not covered automatically.
The complete classical subexponential prime-field ECDLP criterion remains
unmet. [pcc:unverified]

Primary context: maintained Mathlib ZMod.valMinAbs/minimality and existing
UniversalPools owners; pinned Mathlib cfc55fc58714a59dc06e6e79edc6d1d95140d3c2;
Ryan2025 primary pp5--6 and chapter3 for lattice/minima/HHG and independence
scope. KB unavailable, bounded primary/owner fallback, no novelty or absence
claim. [pcc:unverified]
