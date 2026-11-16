#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.5em)
#text(size:18pt,weight:"bold")[Known-target color checksums and the representation budget]
#v(5pt)
16 November 2026 · source a3c5a77 · PCC unverified

A coefficient checksum CAN have a known target: give every record in one
color the same weight. This compatibility layer loses no legal final
vectors. Its separate limitation is that many overlapping representations
share one checksum value. Four shared laws characterize this issue.
No numerical experiment or runtime measurement.

#image("flow.svg",width:100%,height:104mm,fit:"contain")

*Exact common-target characterization.* For finite colors I, a supplied
record choice j0 in J, and weights into an additive commutative group,
#raw("(exists T, forall c:I->J, sum_i lambda(i,c(i))=T)\n  iff forall i,j,k, lambda(i,j)=lambda(i,k)",block:true)
Change one coordinate of a legal tuple, separate that term by the existing
sum-deletion law, then cancel the equal remainder. The converse sums fixed
color weights. This concerns ALL one-per-color coefficient tuples, not just
the subset whose actual group sum is zero.

*Exact image endpoint.* For natural coefficient arrays u with at most K
records per color, natural scalar distribution factors the checksum through
the profile d_i=sum_j u(i,j). Every value comes from I->Fin(K+1), so
#raw("card {H(u): u in V} <= (K+1)^card(I)",block:true)
Actual prime-field point-subgroup and ZMod q endpoints apply the generic
laws unchanged. Profile projection is for this count; full primitive
coefficients still govern compatibility, nonzero provenance and recovery.

#pagebreak()
#text(size:16pt,weight:"bold")[What the filter buys, and what must still be built]

*Known target, no hidden labels.* If w has one unit per color and u+v=w,
then H(w)=T=sum_i lambda_i and H(u)+H(v)=T. The compatibility target is
available without knowing the selected records or their discrete logs.
This is standard linear-checksum algebra, not a novelty claim.

*Hand survival reading.* Fix weights and one solution’s representation
family before sampling an independent uniform residue alpha from Q.
The two split conditions H(u)=alpha and H(v)=T-alpha hold for exactly the
distinct H(u) residues represented by that family. Therefore
#raw("Pr[some representation passes]\n  <= min(1,(K+1)^m/|Q|)",block:true)
Repeated representations in a single profile do not give new residues.
Weights selected in response to alpha require another argument.

For the prior sparse shape, R=binom(m,a) binom(mb-m,h-a) representations
have weight(u)=m+h-2a. When h=O(m), take K=O(m); the image is at most
2^(O(m log(m+1))) even if R contains exponentially many record choices.
At balanced m about sqrt(log2 r), an exponentially large modulus justified
only by R cannot retain constant probability under this residue rule.
Several checksum coordinates still factor through the same profile.

*Scope controls.* This does not rule out small moduli, a deterministic
profile choice, adaptive targets, nonlinear compatibility or joint
point-coordinate filters. K=0 has one profile; b=1 has no within-color
record choice; m=0 is vacuous. The image bound is not a uniform-output law.
A group-dependent filter preserving only actual zero-sum solutions is
outside the universal common-target characterization.

*Next construction.* Use this checksum as a compatibility layer, then
connect efficiently generated compatible families to the actual elliptic
group zero condition. The earlier implicit interval-gcd/block query is one
proposal; its cheap exact implementation and yield/cost bound remain open.
The complete end-to-end algorithm criterion remains unmet.

*Evidence.* Prospective plan1209ad5 and floor682c584 precede sourcea3c5a77.
Focused build003 and actual-group/ZMod assembly001 pass. Failed floor001
and build001 source/logs remain; exact inherited laws fix their API and
equality-interface errors. No proof limit, trust, inventory or linter policy
was weakened. Canonical gate001 audits219 theorems with0 failures and0
trusted-native exceptions. All4 named axiom prints use standard axioms
only. No fresh checker or hosted pass is asserted.

*Primary scope.* Li–Ye sections1.1–1.2 and Randolph–Wegrzycki section2.1
use integer dot-product filters and explicit mixing/generation obligations.
No exponent or all-representation mixing claim is transferred. Wagner2002
sections2–3, Theorem2/Corollary1 supply the cited generic-group comparison;
this study adds a scoped finite profile count, not a general lower bound.
KB unavailable; links and proof map are in the full report. Frozen evidence
stays intact; no native numerical, paid or qualification execution.

Source-linked report: docs/color-checksum-20261116.md
