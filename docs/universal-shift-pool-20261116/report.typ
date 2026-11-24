#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.45em)
#text(size:18pt,weight:"bold")[One shift pool for adaptive two-gate retention]
#v(4pt)
16 November 2026 · shared finite laws · PCC unverified

A simultaneous guarantee can replace selected-output uniformity. Under an
explicit character-density condition, polynomially many known scalar
shifts can cover every ordered point pair at once. Later adaptive choices
then reuse the pool on the same global event. This preserves hidden
representations; it does not extract their original catalog tuples.

#image("flow.svg",width:100%,height:147mm,fit:"contain")

*Domain.* E/Fp, p>3, prime-order subgroup H of size r, k distinct nonzero
anchor abscissas, no two-torsion anchors, 2k smaller than r. Public T_j=jG works.
#raw("κ_j(O)=1; κ_j(P)=χ(x(P)−x(T_j)) otherwise, χ(0)=0.
D={P: every κ_j(P)=+1}; C_W={P∈D: W−P∈D}.",block:true)
The inherited two-gate identity is U+t∈D and V−t∈D iff U+t∈C(U+V).
All original record indices, coefficients, labels and provenance remain.
Tags sG carry known s; opposite additions cancel in the original relation.

#pagebreak()
#text(size:16pt,weight:"bold")[Joint density: the hand analytic argument]

For anchor subsets I,J, define f_I(P)=product(x(P)−x(T_j)) and
S_I={±T_j:j∈I}. Each S_I has size2|I| and group sum0. The mixed function
f_I(P)f_J(W−P) has odd branch support S_I symmetric-difference (W−S_J).

*Noncancellation.* If W≠O and this support vanished, a nonempty subset
would force S_I=W−S_J with a positive common size n≤2k. Sum the reflected
set using inherited finite-sum laws: 0=nW−0. Since order(W)=r>n, this is
impossible. Four shared generic support laws formalize this argument.
Empty subsets and W=O are handled separately.

*Primary framework.* Perret, Acta Arithmetica59(1991), propositions3.1,
3.3,4.3,4.5 and corollary4.6: tame Kummer conductor is the odd branch
support and its character sum has the conductor square-root bound.
Kohel–Shparlinski, section2 propositions1/2 and section3 Lang-isogeny
construction: a finite group character is unramified. Twisting cannot
cancel the mixed function’s nonempty ramification. Conductor degree is
at most2(|I|+|J|), giving that multiple of √p. Averaging over the subgroup
annihilator cancels its index and preserves the same bound on H.
Their additive theorem1 is not imported as a multiplicative theorem.

*Canceled zeros matter.* Ordinary χ(0)=0 can differ from the modified
Artin character at a common even-order zero. Remove the WHOLE set
#raw("Z={±T_j: all j} ∪ {W±T_j: all j},  |Z|≤4k",block:true)
before indicator expansion. Off Z the original and modified terms agree;
even poles at O/W use their specified local units. At Z the actual gate
conjunction is false. Sum all term corrections after division by4^k:
the correction is at most4k, not4^k times4k.

The weighted conductor sum is
#raw("4^(−k) Σ_(I,J) 2(|I|+|J|) √p = 2k √p.
||D|−r/2^k| ≤ k√p+2k.
||C_W|−r/4^k| ≤ 2k√p+4k, for W≠O.",block:true)
For W=O use C_O=D by D=−D; k=0 has D=H. A sufficient explicit condition is
#raw("r ≥ 2 · 4^k (2k√p+4k).
Then |C_W|/r ≥ 1/(2 · 4^k) for every W∈H.",block:true)
The condition holds asymptotically for r comparable to p and polynomial
2^k in log p. It is not automatic for small subgroups or arbitrary k.
These analytic estimates are hand applications, not Lean theorems.

#pagebreak()
#text(size:16pt,weight:"bold")[A finite cap that survives adaptive reuse]

Let A(U,V) be the good shifts for an ordered pair. Translation by U is a
bijection, hence |A(U,V)|=|C(U+V)|. More generally, demand any finite
family of good tag sets A_i of size at least a in a tag type H of size r.
Pools are functions Fin Q→H, including repetitions. Shared finite laws:
#raw("|{pools missing A_i}| = (r−|A_i|)^Q.
|{pools missing some A_i}| ≤ |I| (r−a)^Q.
If |I| (r−a)^Q < r^Q, a pool hitting every A_i exists.",block:true)
The fixed count is an inherited equivalence between constrained functions
and functions into a complement. The union bound is inherited finite-card
counting. Q=0 and empty families are included with their actual semantics.
No enormous function space was enumerated or native-evaluated.

For all r² ordered pairs and the explicit density floor, divide by r^Q
and use 1−x≤exp(−x):
#raw("Pr[any ordered pair misses every pool tag]
    ≤ r² exp(−Q/(2 · 4^k)).
Q = ceil(2 · 4^k (2 ln r + ln(1/ε))), 0<ε<1,
    gives simultaneous failure ≤ ε.",block:true)
The finite count is compiled. The real exponential/logarithmic corollary
is hand arithmetic. The global good-pool event already quantifies over
ALL pairs, so any later adaptively chosen sequence is covered on that
same event. It does not condition a fixed-sequence estimate on the pool.

*Charged use.* Generate Q independent exactly uniform scalar shifts sG
and retain s; charge scalar multiplication, storage and random bits.
A bit-only implementation needs capped exact rejection and a separate
failure budget. For each ALREADY KNOWN pair, scan at most Q tags and2k
characters per tag. Charge group additions, exponentiation and bit costs.
For 2^k polynomial in log p the tag cap is polynomial in log p and
log(1/ε). No implementation, timing or speedup is reported.

*Extraction test.* If every pair has a tag, existentially eliminating
tags rejects no original pair. A hidden original tuple is still hidden.
Root-down splitting of known labels can conserve only a trivial zero
coefficient relation. This pool is a retention interface for the existing
tree result, not a capped implicit-family search or a useful-yield bound.

#pagebreak()
#text(size:16pt,weight:"bold")[Proof boundary and successor mechanism]

*Nine new generic laws.* Four TranslatedSupports laws: sum_reflection,
centered_reflection_nsmul, centered_reflection_ne, sum_symmetric_union.
Five UniversalPools laws: fixed_miss_count, mem_badPools,
miss_union_bound, universal_miss_bound, exists_universal_pool.
Actual Weierstrass prime-field subgroup and quadratic-character predicate
probes apply these laws unchanged. Density remains an explicit input
contract in the semantic endpoint; it is not smuggled in as a proved axiom.

*Audit.* The publication index records the final canonical all-tracked-
source gate and all nine actual compiler axiom prints. No sorry, custom
axiom, native_decide, proof-limit override, linter suppression or source
inventory exception was introduced. Failed floor/source snapshots and raw
compiler diagnostics remain. No fresh independent checker is asserted.
PCC interpretive attestations remain unverified without signed standing.
No evaluated native identity certificate or native/numerical/paid/
qualification run was issued.

*Next discriminating idea.* Test an arithmetic-height extractor directly
against the homogenized S3 equations. Count every numerator and denominator
variable, nonzero-denominator saturation, field-coefficient height,
independent-equation requirement, and total branching frontier. Read the
primary small-root solver assumptions before asserting a determinant or
recovery bound. A short lattice row or a small single-map degree does not
supply a complete solver. Preserve old hypotheses and record corrections
separately.

*Sources checked.* KB tools unavailable; bounded exact pinned Mathlib/
owner search and primary-paper fallback. Perret’s Acta primary printed
pp284–288 was visually read; its modified local-value convention is
essential. Kohel–Shparlinski general character propositions and unramified
Lang-isogeny twist were read. Exact source hashes/URLs/sections are in
source-review001.json. No novelty claim. Existing translated-intersection,
known-tuple tree and pair-colour laws are reused within their scopes.

*Original criterion.* A complete classical subexponential prime-field
ECDLP algorithm still requires capped hidden-tuple extraction and actual
useful nonzero relation yield. The goal remains active.
