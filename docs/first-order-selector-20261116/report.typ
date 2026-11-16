#set page(paper:"a4",margin:16mm)
#set text(font:"DejaVu Sans",size:9.7pt)
#set par(leading:0.4em)
#text(size:18pt,weight:"bold")[Coefficient-first selection in one modular block]
#v(4pt)
16 November2026 · source59cc763 · mathematical model + unexecuted source

The new procedure searches bounded coefficients first, derives compatible
offsets and centers the remaining row. It decides norm-short existence in
p Z^N + Z F(tau), with ONE non-modulus generator. The full integer lattice
has rank N. This bypasses LLL only in the declared model, not in general
ECDLP decomposition. The original complete-algorithm criterion is unmet.

#image("flow.svg",width:100%,height:150mm,fit:"contain")

*Evidence.*44 generic laws, five actual symbolic declarations and one generic
source-table equality compile. Full canonical local audit exits0:347 theorems,
zero failures, zero trusted-native proofs. Two Python files parse; the
selector was not imported or run. No numerical/Sage/curve/LLL, paid or
qualification job. Standard axioms only; no signed verification asserted.

#pagebreak()
#text(size:16pt,weight:"bold")[A complete existence search for the declared family]

Let p be an odd prime, weights positive, and two model coefficients satisfy
#raw("F(tau)[i1]=1; F(tau)[i2]=s*(tau-q), s != 0.
Lambda(tau)=p Z^N + Z F_lift(tau).
L1(c)=sum |c_i| w_i.
n1=floor((p-1)/w1); n2=floor((p-1)/w2).",block:true)
Every p-row on every column is available. Changing the integer lift of
F modulo p does not change this family. Prime certification is the parent's
precondition in the Python library; the library does not certify primality.

*Procedure.* Enumerate nonzero c1 in its first signed window and c2 in the
second. Derive tau=q+c2/(s*c1) modulo p. Center every coefficient of
c1 F(tau). If the row is nonzero with integer L1 below p, retain it and
its exact p-row combination witness. Generic residue candidates are at
most(2n1+1)(2n2+1); the first-endpoint source has exactly2n1(2n2+1) raw pairs.

*Completeness.* A zero scalar modulo p would make every coefficient
divisible by p, so a nonzero row at positive weights could not have L1 below
p. Otherwise the first two coefficients are bounded by the windows and
determine its scalar/offset pair. Coefficientwise centered residues minimize
all positive weighted L1 norms in their congruence class. Thus every existing
short row gives a no-worse centered representative among the candidates.
Anchor1 guarantees it is nonzero. Conversely, the retained p-row witness
places each accepted row in the declared family.

The compiled selected_iff_integer_short theorem expresses that equivalence.
This is a complete EXISTENCE search with one minimal representative per
admissible pair, not enumeration of every integer lift of every short row.
A capped implementation is incomplete unless the whole family is exhausted.

*What it replaces.* No determinant/minima sufficient bound or LLL
approximation factor is needed to decide this block. For higher-rank,
truncated-modulus, or arbitrary saturation blocks, separate arguments are
required. This theorem does not assert certificate existence or root isolation.

#pagebreak()
#text(size:16pt,weight:"bold")[The actual S3 anchors and source correspondence]

For the first endpoint the source uses
#raw("F_tau=(x-y)^2*(U+tau V)^2
 -2*((x+y)*(xy+a)+2b)*(U+tau V)*V
 +((xy-a)^2-4b*(x+y))*V^2.
coeff(x^2 y^2 V^2)=1; coeff(x^2 U V)=2tau.
w1=B^4 H^2; w2=B^2 H^2.",block:true)
Both identities compile by nested univariate coefficient extraction. The
last endpoint with fixed q instead has coefficients1 at x²U² and2(tau−q)
at x²UV. The current Python library implements the FIRST endpoint only.

The polynomial has20 distinct combined monomials. Their exponent map is
proved injective and the full vector expansion equals the endpoint. The
static AST translator reads the coefficient dictionary, checks the same
monomial order and rejects unsupported operations. A generated generic-ring
Lean equality verifies ALL20 source formulas against the formal model.
Neither translation nor compilation runs the selector or field arithmetic.
This is not formal verification of Python control flow or budget handling.

The finite-row laws bound the absolute integer value by weighted L1 and
preserve divisibility through the exact row witness. Compiled monomial
bounds at |x|,|y|≤B and |U|,|V|≤H imply that a selected row vanishes as an
integer at every bounded modular endpoint root. An ECDLP consumer still
needs nonzero-denominator, original point/sign and relation checks. A single
vanishing equation can be dependent or leave positive-dimensional roots.

*Why sample coefficients.* All compatible offsets lie in an inverse-scalar
image of the two windows. Its cardinal and finite-pool miss bounds compile.
A hand union bound gives hit probability at most
Q(2n1+1)(2n2+1)/p for Q iid uniform offsets. If all these quantities are
p^o(1), the bound is p^(−1+o(1)). The direct selector enumerates that sparse
image instead of assuming a uniform pool will encounter it.

At H≈sqrt(p)/B^kappa, fixed kappa>2, candidates number O(B^(4kappa−6)).
For B=p^o(1), fixed20 columns and bounded input bit lengths, the declared
search has subexponential arithmetic/output cost. This is HAND complexity
accounting, not measured speed or runtime qualification.

#pagebreak()
#text(size:16pt,weight:"bold")[Complete-empty is scoped; ECDLP yield remains open]

The source reuses one shared pair/certificate budget across models, reserves
the whole candidate family before search, and retains every visited pair,
row and rejection. Equal polynomials do not erase pair records. Accepted
rows include scalar, offset, source coefficients, weights, centered row,
exact L1 and the integer modulus-row witness. Large integers are strings.

A completed search may report complete_empty or complete_nonempty only in
this declared block. Any preflight/output/certificate/deadline interruption
means incomplete and cannot certify absence. The parent must retain events,
reserve terminal result space and enforce process/memory/deadline limits.
The library includes no implicit experiment authorization or launch request.

*Formal scope.* Eight field-rectangle, five coefficient-window, twelve endpoint,
sixteen rank-one search and three weighted-row laws:44 generic named laws.
Five actual declarations and the AST-translated table equality compile.
Canonical347/0/0 exits0. Every actual named axiom print uses standard axioms.
Raw compiler failures and warning whitespace are preserved. No proof-limit,
trust/inventory/linter exception, sorry or native_decide was introduced.

*The missing intersection.* Coefficient-selected offsets are nonuniform.
Uniform chart-pool coverage cannot be carried over to them. We need enough
certificate-compatible offsets that also represent useful original
point decompositions. No lower bound for that intersection or random-target
yield is proved. Finite root recovery, independence and complete cold scalar
recovery cost remain open. Component completeness is not ECDLP completeness.

*Execution.* The Python implementation remains UNEXECUTED; two syntax parses
and source-table algebra are distinct from a numerical trial. No measured
speed, success panel, native qualification, paid build/job or signed verifier.
Live cost/reservation balance, source-image custody and actual caller/capacity
admission are still missing. Three bounded project-name searches in connected
Drive found no matching budget record; that is not a zero-spend assertion.

*Next discriminating work.* Under the existing admission rules, compare this
exact search with a direct full residue scan on a small frozen known-answer
case, preserving complete/empty/capped outcomes and all witnesses. That would
test implementation only. Then investigate structured-shift coverage and
independent useful equations, or higher-rank coefficient search. The complete
classical subexponential prime-field ECDLP criterion remains unmet.

*Provenance.* Mathlib ZMod.valMinAbs/minimality and UniversalPools, pinned
cfc55fc58714a59dc06e6e79edc6d1d95140d3c2; Ryan2025 primary pp5–6 and chapter3
for norm/minima/HHG and independence scope. KB unavailable; bounded primary/
owner fallback, no novelty or absence claim. PCC attestation unverified.
