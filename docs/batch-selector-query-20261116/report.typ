#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.5em)
#text(size:18pt,weight:"bold")[Arbitrary-subtotal retention and batch queries]
#v(5pt)
16 November 2026 · shared source b4b9f52

The actual two-gate event now has a shared finite interface for every
subtotal W, including nonzero W. A separate hand character-sum application
gives an interval-intersection estimate with explicit hypotheses. A fast
block query and the full multilevel cost remain open. PCC is unverified;
no numerical/timing experiment was run.

#image("flow.svg",width:100%,height:111mm,fit:"contain")

*Checked finite component.* For arbitrary U,V in a finite additive group,
put W=U+V and Cw=S intersect(W−S). Then
#raw("[U+t in S AND V-t in S] iff [U+t in Cw]\nq(W)=|Cw|/|G|; single-tag variance=q(W)*(1-q(W))",block:true)
The seven shared laws retain the original acceptedCount, with no zero-target
or symmetry hypothesis. They apply existing shifted-hit laws to this actual
subset. The final probe applies them unchanged at actual ZMod p Weierstrass
subgroups, inheriting finiteness. For W=0 and S=−S, C0=S recovers the prior case.

#pagebreak()
#text(size:16pt,weight:"bold")[The interval estimate and the state-growth test]

*Hand analytic application, separately scoped.* Let E/Fp be nonsingular
short-Weierstrass, p>3; H a subgroup of order r; I a cyclic interval of
length L; S={P in H excluding O: x(P) in I}; alpha=L/p. For every nonzero W in H,
#raw("abs(|Cw|-(r-2)*alpha^2) <= 8*sqrt(p)*(1+ln p)^2",block:true)
Expanding both interval indicators uses f(P)=a*x(P)+b*x(W−P). For nonzero
a,b, its distinct double poles at O,W give degree4 and prevent pole
cancellation or Artin–Schreier degeneracy. Kohel–Shparlinski’s subgroup
bound gives8sqrt(p). One nonzero frequency uses degree2 plus one excluded
point; the same safe bound covers it. Their interval Fourier-L1 bound
provides the log-squared factor. Both-trivial frequency contributes r−2.
W=O is handled separately by symmetry and the single-interval bound.

With b>=1, L=floor(p/b), p>=2b, r>=4 and
#raw("r >= 128*b^2*sqrt(p)*(1+ln p)^2",block:true)
these hand inequalities give q(W)>=1/(16b²) for all W, so k=16b² raw
independent shifts retain a fixed subtotal with probability at least1−exp(−1).
This does not apply to arbitrary tiny subgroups or every random marker
threshold. It is not a formalized character theorem or a selected-state law.

*Which cost matters.* A b³ subroutine at fixed height can fit the balanced
subexponential target. The missing bound is growth across all m colors.
For raw independent size-b color lists and a fixed current filter of density
delta, independent of the lists, all Ns=b^s partial tuples give
#raw("E Xs=Ns*delta; Var Xs=Ns*delta*(1-delta)\nPr[Xs < E Xs/2] <= 4/(Ns*delta)\nE retained equal-subtotal pairs=Ns*(Ns-1)*delta/(2r)",block:true)
These hand counts use pairwise independent distinct-tuple sums. At Ns of
order sqrt(r), delta of order1/b, complete whole-level materialization has
about sqrt(r)/b states with few point collisions. This scopes one explicit
single-current-filter architecture; lazy, selective, adaptive, multi-filter
and implicit methods require their own analysis.

#pagebreak()
#text(size:16pt,weight:"bold")[A proposed decision primitive before expansion]

*Exact block query.* For index blocks A,B, decide whether any actual pair
(a,j) passes kappa(Ua+Tj)<=tau. With charged compact preprocessing and cheap
exact block decisions, binary self-reduction could recover K hits using
O((K+1)log(NM)) queries plus metadata/output work. Repeated per-query scans
are charged; they need not fit this bound. Randomized sketches also need
explicit false-negative and false-positive work bounds.

*Concrete algebraic candidate.* Retain the product RAB(Z) of Z−x(Ua+Tj)
over affine sums implicitly. A positive-degree gcd with the interval product
FI(Z)=product over z in I of (Z−z) detects a finite hit. Repeated roots retain
pair multiplicity; infinity hits need a separate opposite-point query when
the gate includes O. Actual indices and primitive provenance still need recovery.
Explicit degrees are |A||B| and about p/b. No fast implicit update/interval-gcd
implementation or bound is supplied. Writing a compact product is insufficient.

*What the primary methods supply.* BGGKU theorem1.1 takes a coefficient
vector and explicitly supplied evaluation points. ECFFT theorem7.2 evaluates
on a fixed supplied set; its auxiliary smooth-order curve does not change
the target group. Applying either to every raw pair still supplies the grid.
Warren’s finite-field cubic result bounds incidence counts rather than
implementing pair reporting. Bostan–Gaudry–Schost’s interval products do not
supply this arbitrary compressed block/quotient-ring oracle. A 2026 modular-
factorial preprint was checked only at abstract level; no bound is imported.

*Evidence.* Prospective plan fdb4470, inherited floor c62ae17, source b4b9f52.
Focused build and actual-field probe pass. Canonical gate001 audits212
theorems,0 failures,0 trusted-native exceptions. All7 new named axiom prints
use only propext, Classical.choice and Quot.sound. Original floor001 failures
remain; floor002 passes after argument-order/context corrections. No limit,
trust, inventory or linter policy changed. No fresh checker or hosted pass.

The original complete-algorithm criterion remains unmet: charged multilevel
state construction, actual useful yield and full witness/scalar recovery
still need a constructive bound. The numerical panel still needs checkpoint
access. Frozen crypto4311/4338/4352 histories and old owner claim subjects
remain untouched. There is no measured value/algorithm edge to update in
canonical graphs; this diagram records the exact/hand/proposed boundaries.

*Primary links.*
#link("https://arxiv.org/html/2205.00342")[BGGKU];
#link("https://arxiv.org/html/2107.08473")[ECFFT];
#link("https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf")[Kohel–Shparlinski];
#link("https://arxiv.org/html/2211.09465")[Warren];
#link("https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf")[Bostan–Gaudry–Schost].
KB unavailable; bounded fallback and exact reading scope in the full report.
No novelty claim. See ../batch-selector-query-20261116.md for all assumptions.
