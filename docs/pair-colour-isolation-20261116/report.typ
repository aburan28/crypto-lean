#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.45em)
#text(size:18pt,weight:"bold")[Pair-colour isolation and useful-subset coverage]
#v(4pt)
16 November 2026 · source a39b093 · PCC unverified

A bounded candidate-list design for the actual one-character elliptic
pair graph. Standard pairwise isolation supplies a lower bound on reaching
any fixed useful subset without assuming that a witness finder samples
uniformly. Shared finite laws and actual instances compile locally;
wrapper/recovery/cost are hand reasoning, not measured implementation.

#image("flow.svg",width:100%,height:135mm,fit:"contain")

*Interface.* Two explicit original point-record lists, lengths N,M.
Let S be all indexed pairs passing the anchor quadratic-character gate,
g=|S|>0, and T⊆S a useful subset fixed before colours. Set θ=|T|/g.
Empty input returns an empty list. Keep all original record indices,
coefficients, labels and provenance, including repeated point values.
Do not construct an implicit Cartesian family for free.

#pagebreak()
#text(size:16pt,weight:"bold")[Finite count and why the sampler reaches useful pairs]

*Product-compatible colours.* At level ell, choose independent uniform
r_i,c_j in H=(F₂)^ell. Retain pair e=(i,j) if h_e=r_i+c_j=0.
Matching-colour buckets partition all explicit records; total side length
across buckets is N+M. Iterate occupied buckets only, with no loop over
B=|H|. Repeated point records are independent colour coordinates.

The edge map is an additive hom from Ω=(I→H)×(J→H) to H. For two distinct
record pairs, the combined map to H×H is surjective: distinct rows permit
two arbitrary row colours; otherwise the two columns are distinct and
permit arbitrary column colours. Existing equal-fiber scaling gives
#raw("B |A_e| = C;  B^2 |A_e intersect A_f| = C for e != f;
A_e={omega: h_e(omega)=0}, C=|Omega|.",block:true)
Only pairwise independence is used. Four-cycle hash correlations remain.

*Exact finite isolation.* U(e)=A(e) minus the union of A(f) over f∈S, f≠e.
The subtraction removes ALL other passing pairs, not only useful ones.
Finite union bounds give |A_e|≤|U_e|+sum_f≠e |A_e intersect A_f|.
The U_e for different target e∈T are disjoint. Sum and scale:
#raw("|T| C B <= B^2 |union_(e in T) U_e| + |T|(g-1)C.
If B >= 2g and B>0: |T| C <= 2B |union_(e in T) U_e|.",block:true)
These finite laws and the actual colour-fiber endpoint are compiled.
For uniform Ω, isolated-target probability is at least |T|/(2B).
One tested dyadic scale satisfies 2g≤B\<4g, yielding θ/8.

*Singleton recovery.* Run all direct exceptional-case scans INSIDE each
selected bucket, then all-row parity with column mask1. If there is one
passing edge globally after hashing, earlier buckets cannot return a
checked pair and its own bucket must recover it. On larger graphs the
finder may be biased or miss an even graph; the isolated event still
forces the target output. No global pre-hash direct return is allowed.

Try all L=ceil(log₂(2NM)) scales, keeping at most one pair per scale.
Any fixed useful T is hit with probability at least θ/8 in the full
candidate list. Check every candidate, continuing after nonuseful ones.
Independent complete rounds give miss≤(1−θ/8)^q at a supplied cap q.
This is a coverage bound, not a uniform-single-output assertion.

#pagebreak()
#text(size:16pt,weight:"bold")[Charged cost, checked scope and the remaining construction]

*Hand cap.* With L dyadic levels and q rounds:
#raw("O~(q L (N+M)) field operations + O(q L V) full validation;
O(q (N+M) L^2) random bits; at most q L candidates.",block:true)
V includes primitive coefficient/label recovery, compatibility and final
curve/scalar checks. Sum the actual per-bucket polynomial arithmetic and
exceptional cases, record-colour construction, sorting and failed trials.
All original metadata is retained via references. Input bit costs and
polynomial logarithmic field-arithmetic factors are charged separately.
No implicit family, joint oracle, timing or measured speedup is supplied.

*Proof scope.* Eleven new named laws in shared FiniteIsolation and
PairColourIsolation. Existing finite-card union/sum laws and the finite
additive-hom fiber theorem are applied unchanged. Actual F₂-vector colours
and an actual prime-field elliptic point-sum graph instantiate the count.
Canonical gate001 reports247 audited theorems,0 failing and0 trusted-
native exceptions. All11 actual named compiler axiom prints use only
allowed standard axioms. No fresh independent checker is available.
The dyadic probability, bucket recovery, list wrapper, useful-predicate
validation and asymptotic accounting are hand analysis. Original failed
sources/logs stay intact; no proof-limit, trust or linter policy exception.

*A precise dependency.* A justified useful fraction θ would now transfer
to a bounded candidate cap without output-uniformity assumptions. For
θ≥2^(−O(m log(m+1))), a matching cap fits the earlier selector target.
The actual θ bound, cheap implicit-family construction and simultaneous-
gate reporting remain open. Individual and subset-XOR parities do not
supply AND parity. Original complete prime-field ECDLP criterion: unmet.
No numerical/native cases, paid jobs or qualification execution.

*Sources / comparison.* Valiant–Vazirani1986 proof pp87–90 supplies standard
isolation context; this is not a novelty claim. Addanki–McGregor–Musco2022,
full Algorithm6/Theorem38, gives stronger near-uniform edge sampling under
exact BIS queries; its graph-query complexity is not a total elliptic cost
or an implemented noisy-oracle reduction here. Dumas–Pernet–Saunders2009
describes n pure black-box matvecs for trace and allows faster structured
methods; it is not an elliptic impossibility theorem. Exact Mathlib names,
input contracts and primary URLs are in the Markdown report and plan.
KB unavailable: bounded primary/source fallback. No performance data are
plotted and no canonical benchmark/leaderboard graph is changed.
