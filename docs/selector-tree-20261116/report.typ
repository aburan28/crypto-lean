#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.5em)
#text(size:18pt,weight:"bold")[Tree representations and the root shortlist budget]
#v(5pt)
16 November 2026 · source 0ad8012 · PCC unverified

The new finite count allows arbitrary selection within one input half,
without assuming uniform selected outputs. It tests a bounded independent
root-list architecture. A separate known-tuple construction preserves tree
constraints, but does not find the hidden tuple. Joint alternatives remain
proposed. No numerical or timing experiment.

#image("flow.svg",width:100%,height:111mm,fit:"contain")

*Exact shared endpoint.* Let A be first-world information/coins, independent
of raw right records x:(Fin s x Fin b)->G, s>0, r=|G|. Any F:A->Finset G
with |F(a)|<=L satisfies
#raw("card{(a,x) | exists g in F(a),c: tupleSum(c,x)=g} * r\n  <= card(A)*L*b^s*r^(s*b)",block:true)
The hand raw-probability reading is success<=min(1,L*b^s/r). Targets can
be negative left subtotals. Selection may use arbitrary left coordinates;
the restriction is lack of access to the sampled right array. Existing
equal-fiber, surjection-card and Sigma-cardinality laws supply the proof.
The final probe applies it unchanged at actual prime-field point subgroups.

#pagebreak()
#text(size:16pt,weight:"bold")[What survives through a complete tree]

*Hand supplied-witness constructor.* Its input already includes a chosen
tuple X1,...,Xm with sum0. Precompute subtree subtotals. A node with original
subtotals U,V and incoming offset a tries local t and sends offsets a+t and
−t to its children. Their outputs U+a+t and V−t add to U+V+a. Descendants
therefore preserve the admitted ancestor value.

With a fixed symmetric S and q(W)=|S intersect(W−S)|/r>=q0 for every W,
reveal each node’s independent uniform pool only when visiting it. Choose
the first passing tag. For J=m−1 nodes and k shifts per pool,
#raw("Pr[failure] <= J*(1-q0)^k <= J*exp(-q0*k)\nk >= ln(J/epsilon)/q0 gives success >= 1-epsilon",block:true)
The previous hand fixed-interval estimate gives q0=1/(16b²) under its
explicit p>3 and large-subgroup condition. Then k=O(b²log(m/epsilon)).
This does not apply to every random marker threshold or to an unanalysed
clean-conditioned pool. These tree statements are hand analysis here.

Charge O(mk) pool tests/group operations plus point generation, key work,
provenance and final checks. Scalar-multiple sampling adds O(mk log r)
group operations. Each local auxiliary coefficient enters child subtrees
with opposite signs; root addition retains the original nonzero coefficient
vector. A local planted-zero output is not substituted for that vector.

The constructor reads both subtotals of the supplied witness when choosing
tags. It does not supply an independent-half extractor for an unknown tuple.
Enumerating all tuple/context states may still cost much more.

*Hand consequence of the exact root budget.* For balanced
m about sqrt(n), b=ceil(r^(1/m)), s about m/2,
#raw("success <= L*2^(-n/2+O(n/m+m))",block:true)
If the explicit first-side target cap L fits the proposed balanced per-attempt
bound, in the standard input-bitlength regime this misses the useful-yield
target. No uniform output assumption is required. Conditioning on global
clean rejection needs its own division by Pr(clean).

This scopes targets formed without right-input access, even if every original
right tuple is later considered. Shared independent pools must count all
submitted targets. Right-dependent context generation, exponentially large
implicit target sets, overlapping supports and other output contracts are
outside this theorem. It is not a general ECDLP or selector lower bound.

#pagebreak()
#text(size:16pt,weight:"bold")[A concrete overlapping-support successor]

*Different information flow.* Keep a final one-per-color coefficient vector
w, but split it over all original records into u in {0,1} and v in {−1,0,1}:
#raw("w_i=0: (u_i,v_i)=(0,0) or (1,-1)\nw_i=1: (u_i,v_i)=(1,0) or (0,1)",block:true)
Both parts may use records from every color, so the independent completion
space does not model them. These are established representation identities,
not a novelty claim. A sparse shape chooses a selected coordinates with
v=+1 and h−a unselected coordinates with v=−1, giving the hand count
#raw("R=binom(m,a)*binom(B0-m,h-a)\nweight(v)=h; weight(u)=m+h-2a",block:true)
The search must recover compatible vectors whose sum has exactly one unit
coordinate per color, with no negative/2 entries and nonzero full provenance.
Group equality alone is insufficient. Private-label recovery stays outside
the point-only selection process.

Filtered generation of these overlapping sparse families, or an implicit
block/interval-gcd decision depending on both inputs, are concrete next
interfaces. Neither has a charged construction/yield bound. Integer
dot-product modular filters and compatibility-circuit exponents are not
transferred to elliptic encodings. A checksum whose target is unknown adds
its own success loss.

*Evidence.* Plan8b8ea10 and inherited floor22614e8 precede source0ad8012.
Focused build002 and actual-field probe pass. Canonical gate001 audits215
theorems,0 failures,0 trusted-native exceptions. All3 named axiom prints
use only standard allowed axioms. Original floor001 and build001 sources/
logs remain. No mathematical hypothesis, proof limit, inventory, trust or
linter policy was weakened. No fresh checker or hosted pass is asserted.

*Primary scope.* HGJ2010 slides9–14 and Wagner sections2–3 establish the
representation/filter context. Randolph–Wegrzycki sections2.1–2.3/3.1 and
Li–Ye sections1.1–1.2 use supplied integer dot products for modular filters
and allow overlapping supports. No algorithmic exponent is imported here.
KB unavailable; exact reading links and declarations are in the full report.

#link("https://www.iacr.org/conferences/eurocrypt2010/talks/knapsacks.pdf")[HGJ];
#link("https://people.eecs.berkeley.edu/~daw/papers/genbday.html")[Wagner];
#link("https://arxiv.org/html/2511.10823")[Randolph–Wegrzycki];
#link("https://arxiv.org/html/2610.10446")[Li–Ye].

The complete end-to-end criterion remains unmet: joint implicit construction,
actual useful yield and full witness/scalar recovery still need a capped
bound. Frozen owner/consumer evidence stays intact. No measured value or
completed-algorithm edge changes in canonical graphs. Full report:
../selector-tree-20261116.md.
