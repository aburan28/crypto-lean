#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.55em)
#text(size:18pt,weight:"bold")[Two-point completions and the anchor search]
#v(5pt)
15 November 2026 · candidate B · source 6ff0006

The centered-coordinate completion interface is locally checked. A shared
pair table gives an explicit batch baseline; implicit anchor lifting remains
open. PCC standing is unverified. No numerical or timing result is reported.

#image("flow.svg",width:100%)

*Exact coordinate interface.* Use actual Mathlib Weierstrass points and the
existing normalized representative #raw("key_S(P)=xRep(P-S)"), including infinity.
#raw("key_S(P)=key_S(Q) iff P=Q or P+Q=S+S\nIf P!=Q and S+S=T: key_S(P)=key_S(Q) iff P+Q=T",block:true)
The shared source composes Mathlib’s exact x-fiber law and subtraction
identities. It introduces no replacement group or coordinate. The final
prime-field assembly reads P+Q=−A as (P+Q)+A=0. The half-target hypothesis
and diagonal exclusion remain explicit.

*Hand pencil bridge.* For anchor divisor D of degree m−2, write A=mO−D
and T=−sum(D). In the odd-order subgroup, public scalar (r+1)/2 supplies
S=T/2. The standard divisor-class argument gives A∼2S; multiplying by a
common rational function identifies L(A) with L(2S). The latter is spanned
by 1 and x(P−S). A basis change gives the same extended projective fibers.
Fixed zeros and poles require the linear-system interpretation, not raw 0/0
evaluation. This function-space bridge is hand mathematics, not a new Lean law.

*Evidence.* Lean4.35.0 / Mathlib cfc55fc. Both source laws build; generic
and actual prime-field assembly pass. Canonical gate001 audits169 theorems,
0 failures,0 trusted-native exceptions. Both axiom prints use only propext,
Classical.choice and Quot.sound. No fresh lean4checker result is asserted.

#pagebreak()
#text(size:16pt,weight:"bold")[What batching still has to construct]

*Charged explicit baseline.* Enumerate all b² pairs of the final two colors
once and store their actual group sums with record provenance. For every
supplied anchor D, compute T=−sum(D) and query this dictionary. Include exact
point encoding/equality, dictionary work, record recovery and final checks.
#raw("Pair table: b^2 group additions and O(b^2) records\nK supplied anchors: O(K*m) group additions plus K queries\nAll anchors: K=b^(m-2)",block:true)
Hashing has expected data-structure costs; sorting gives a deterministic
logarithmic-factor alternative. These are hand operation counts, not a
measured program. The centered pencil need not be evaluated for this baseline.

*Scoped yield analysis.* Suppose at most K anchors are selected using only
the first m−2 colors and independent coins. The family must be independent
of the last two colors. On the original raw independent uniform group law,
linearity gives E[Z]≤K·b²/r for the count of all anchor/pair completions.
Neither different pairs nor different anchors need be independent.

Let C reject infinity and repeated abscissas across B₀=m·b records.
The exact x fibers have size at most2, so a union bound gives
#raw("Pr(C) >= 1-B0^2/r\nPr(any completion | C) <= K*b^2/(r*Pr(C))",block:true)
At balanced m≈√n, b≈r^(1/m), n=ceil(log₂r), subexponential K gives an upper
bound 2^(−n+o(n)), below the proposal’s useful-yield target. This is hand
probability/asymptotic analysis for the specified family-selection schedule.
It does not cover future-aware/adaptive selection, implicit-family lifting
or a different selector architecture.

*Next constructive interface.* Given the b² pair-target set and the other
m−2 colors, lift one target to actual anchor records without expanding an
exponential family. A compressed translation operator would need a closed
state, charged updates, a zero-test and witness extraction. An unevaluated
exponential product does not meet that contract. No such implementation or
cost/yield proof is supplied; the complete-algorithm criterion remains open.

*Receipts and sources.* Plan b3be549 and floor0c9bcd4 precede source6ff0006;
assembly7bc6d4c applies the laws unchanged. Original floor001 omitted the
generic DecidableEq instance; assembly001 omitted ZMod’s Field import.
Both failed sources/logs remain. Required instances/imports were supplied
without changing the laws, limits, source inventory or trust policy.

#link("https://crypto.stanford.edu/pbc/notes/elliptic/divisor.html")[Lynn, divisors];
#link("https://websites.umich.edu/asnowden/teaching/2013/679/L02.html")[Snowden, lecture2];
#link("https://arxiv.org/html/cs/0507026")[Cheng, section2].
KB unavailable; no novelty claim. Full scope/proof map: ../centered-completion-20261115.md.
