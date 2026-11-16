#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.45em)
#text(size:18pt,weight:"bold")[One-character elliptic pair search by row parity]
#v(4pt)
16 November 2026 · source e730b61 · PCC unverified

A construction for finding a pair of explicit elliptic points whose sum
passes one quadratic-character gate. Two univariate product/remainder
trees compute every row parity under one random column-record mask.
The procedure below has a fixed attempt cap and preserves repeated records.
Shared component laws compile; the search and cost are hand reasoning,
not an implemented or measured selector.

#image("flow.svg",width:100%,height:131mm,fit:"contain")

*Predicate.* Fix T=(a,b), with −T=(a,b_minus), on an elliptic curve over
F_p, p>3. Define κ(O)=1 and κ(P)=χ(x(P)−a). In the nonvertical chart,
#raw("κ(P+Q) = κ(P) κ(Q) χ((z+(P)−z+(Q))(z−(P)−z−(Q)))
z±(P) = (y(P)−y(±T))/(x(P)−a)",block:true)
The inherited addition-polynomial norm gives two line values with the
same scale. Its square cancels under χ. Actual ZMod p point-addition
assembly applies the shared law unchanged.

#pagebreak()
#text(size:16pt,weight:"bold")[Complete procedure for the one-character primitive]

*Input and output.* Two explicit point-record lists A,B of lengths N,M,
anchor T and trial cap t. Return original indices of a pair with κ(P+Q)=1,
checked by group addition, or NO_WITNESS_FOUND. Each mask bit belongs to
an original column record, even when points or keys repeat.

1. Build point-value dictionaries retaining full record buckets. Scan all
   pairs involving input O,T,−T through at most six linear passes. Test
   coincidence by κ(2P); find inverse pairs by lookup, since κ(O)=1.
   Return if any passes. Failed direct tests justify excluding only those
   nonpassing pairs/buckets from active search.
2. For a remaining row P, deduplicate D(P)={P,T−P,−T−P}. The union of
   zero-key partners lies in these at most three point values. Distinct
   zero-key pairs sum to ±T and have character0; coincident pairs were
   already tested. No remaining passing pair is removed.
3. Select each active column RECORD independently with probability1/2.
   Keep the selected indices and counts n_Q per point value. Form
   F±(X)=∏selected_records(X−z±(Q)), including every repeated factor.
4. For each distinct row key u, let m_u count selected columns at u.
   Compute H±(u)=[X^m_u]F±(X+u). This equals the product of all NONZERO
   key differences. Use remainder trees modulo (X−u)^(m_u+1), then
   characteristic-independent Taylor shifts. No derivative/m_u! formula.
5. Remove D(P)'s remaining NONZERO factors at each anchor, with their
   selected multiplicities. Divide H± by these nonzero correction
   products to obtain G±. Remove the same buckets' unary signs/counts.
6. With k_P admissible selected columns and U_P their κ(Q) product, form
   R_P=(−1)^k_P κ(P)^k_P U_P χ(G+G−). It equals ∏admissible(−κ(P+Q)).
   Therefore R_P=−1 exactly when that row has an odd passing count.
7. If a row is odd, scan its selected columns and check actual group sums;
   oddness guarantees a passing indexed pair. A failed recovery after odd
   parity is an implementation error. If no row is odd, try the next mask,
   stopping after t masks. A failure output never certifies emptiness.

*Exact correction.* Stripping zeros separately is insufficient: a partner
zero at one anchor may leave a nonzero factor at the other. The generic
quotient law removes the whole forbidden union's remaining nonzero factors
and proves that its denominator is nonzero. Full record multiplicities
remain in both the Taylor coefficient and correction exponents.

#pagebreak()
#text(size:16pt,weight:"bold")[Probability, cost and checked component scope]

*Probability, for any fixed input.* Let M have1 exactly at remaining
passing indexed pairs. All row signs encode M c over F₂. A nonzero row
is a surjective linear functional, hence exactly half of raw column masks
make that row1. Its one-fiber is contained in {c:M c≠0}. Thus a nonempty
matrix is detected with probability at least1/2 per independent mask;
t masks miss with probability at most2^(−t). No input-point or selected-
output uniformity assumption is used. Returned pairs are checked.

*Charged hand bound.* For one anchor, distinct row keys satisfy
sum_u(m_u+1)≤M+N. Product/remainder trees therefore have total modulus
degree O(N+M). Translate each leaf remainder by recursive polynomial
splitting: shift(f_low+X^k f_high)=shift(f_low)+(X+u)^k shift(f_high).
This uses no factorial inverses and works when m_u≥p. Standard fast
univariate arithmetic gives quasilinear cost up to logarithms. Count both
anchors, dictionary preparation, at most three corrections per row,
character evaluation, failed masks, t M random bits and one linear witness
scan. Total O~(t(N+M)+N+M) field operations, with polynomial logarithmic
bit overhead; quasilinear working space for sequential masks. No numerical
run, runtime measurement or speed comparison is supplied.

*Proof boundary.* Seventeen named theorems in shared BilinearSketch,
ProjectiveProducts and CharacterCarry, plus actual prime-field and F₂
assemblies. Existing equal-fiber, matrix, polynomial Taylor/resultant,
finite-product and Weierstrass laws are applied unchanged. All defaults
are retained; failures and original source snapshots are preserved.
Canonical gate002 audits236 theorems, with0 failing and0 trusted-native
exceptions. All17 named compiler axiom prints use only the standard
allowed axioms. No fresh independent checker or hosted pass is asserted.
The exceptional-point identification, full search/cost and multiplication
of repeated-trial probabilities are hand arguments, not extra Lean claims.

*Next missing construction.* Several individual gate parities do not give
the parity of their AND. Products of quadratic characters impose XOR.
For two binary matrices the conjunction count parity is trace(M1 M2ᵀ);
separate cheap matvecs alone do not provide a cheap exact trace. Exploit
the actual pair algebra for a conjunction oracle, or choose a selector
whose entire required gate already admits an aggregate. Implicit partial
families, useful m-color relation yield and label recovery remain open.
The user's complete ECDLP algorithm criterion is unchanged and unmet.

*Sources.* Borodin–Moenck, Fast Modular Transforms (1974), pp372–374,
product/remainder-tree recursion; Moroz–Schost, truncated-resultant paper,
intro (univariate context only); Galbraith–Smith and Dechene for carry/
extension context; exact pinned Mathlib declarations listed in the full
Markdown report. KB unavailable: bounded repository/primary-source fallback.
No literature novelty claim. No canonical performance graph is changed.
