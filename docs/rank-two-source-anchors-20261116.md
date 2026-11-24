# A curve-dependent rank-two selector and its curve-code limit

16 November2026. New attempt: retain the two original S3 sources F1W² and F2,
instead of canceling b into a single primitive. The complete classical
subexponential prime-field ECDLP criterion remains unmet. Sixteen generic laws
and four actual source applications compile. No numerical/field/curve/LLL/native
qualification/paid execution occurred. [pcc:unverified]

## Source and exact anchors

Use the frozen first and adjacent sources, translated by Z=U+tau V,T=X+sigma W:

    J = lambda*W²*F1 + mu*F2.

This has chart profile(2,2). Both original zeros remain zeros of J. The compiled
b-difference is -4bVW*(lambda*W*A1+mu*A2), so this is genuinely the curve-dependent
two-source span, not the canceled primitive. The source coefficient at x²y² is
lambda*V²W², regardless of the translated coordinates. [pcc:unverified]

The actual projective coefficient extraction first takes T and U degrees, then
the constant leaf-w coefficient, then V and W degrees. Leaves x,y remain arbitrary
parameters and the extracted values are independent of them. Five exact anchors
of the ENTIRE source are compiled, including the V/W extraction:

| T | U | w | V | W | value |
|---|---|---|---|---|---|
|2|2|0|0|0|mu|
|2|1|0|1|0|2mu*tau|
|1|2|0|0|1|2mu*sigma|
|1|1|0|1|1|2mu*(2tau*sigma-a)|
|1|0|0|2|1|2mu*(tau²*sigma-a*tau-2b)|

This is coefficient extraction, not evaluation at selected leaf values. Every
row above has the same projective weight L=H1² H2² and no leaf-B factor. The
coefficient values hold over any commutative ring. [pcc:unverified]

Over a field with2mu!=0, let the last four anchors be c,d,e,k. The compiled decoder is

    tau=c/(2mu); sigma=d/(2mu);
    a=2tau*sigma-e/(2mu);
    b=(tau²*sigma-a*tau-k/(2mu))/2.

Thus the same cheap anchors that recover the chart ALSO encode the curve. Signed
scalars are allowed. The exact mu=0 branch remains lambda*W²*F1 and is independent
of sigma; it is explicitly retained rather than divided away. [pcc:unverified]

## Candidate fast selector — hand algorithm, not implemented

For an integer row congruent to J modulo p with weighted norm<p, let
T=floor((p-1)/L). Its integer lifts of mu,c,d have magnitude<=T, and the lambda
anchor has magnitude<=floor((p-1)/(B⁴ L)). Enumerate those four integer windows,
keep mu!=0 modulo p, decode tau,sigma, reconstruct and center the ENTIRE source
row, then check its full weighted norm and exact modulus witness. Retain each
parameter/row block with its multiplicity. Only the existence of a centered
norm-minimal lift is intended; it is not enumeration of every integer lift.
[pcc:unverified]

The straight box-search candidate count is at most
(2floor((p-1)/(B⁴L))+1)*(2T+1)^3. At fixed support and L=p^(1-o(1)) this is p^o(1).
No p-offset scan is required in the nonzero-mu branch. A mu=0 fibre needs its own
first-equation selector and a symbolic free second offset; expanding that free
fibre would itself cost p. Full capped selector existence equivalence, source
implementation and measured runtime are NOT supplied. [pcc:unverified]

## The discriminating count

For any finite field-element window S, a compiled finite image construction takes
five entries(mu,c,d,e,k) from S, with mu!=0, and decodes a curve(a,b). Its cardinality
is at most |S|^5. Actual source membership, same-code curve uniqueness, and cover
from any bounded integer lifts of these five source anchors compile. For the
image of the integer window[-T,T], the compiled bound is(2T+1)^5. Division by2 and
mu is always explicit; no curve distribution premise enters this finite theorem.
[pcc:unverified]

The full mod-p polynomial-row and weighted-norm transfer remains HAND: all five
actual anchors have weight L, so any norm-short row in this declared span with
mu!=0 gives integer lifts bounded by T. Therefore, at fixed support and near-critical
L=p^(1-o(1)), only p^o(1) coefficient pairs(a,b) can occur, among p² possible pairs.
Uniform nonsingular short-Weierstrass models consequently have density at most
p^(-2+o(1)); the O(p) singular models do not change this exponent. Taking a union
over p^o(1) declared configurations preserves this bound. Even a union over all
standard short-Weierstrass coordinate scalings changes it by at most a factor p,
not enough to establish generic useful yield. These asymptotic/model transfers
are hand arguments, not a newly compiled probabilistic ECDLP theorem.
[pcc:unverified]

The finite diagnostic also explains the tradeoff: to cover order p² curve models
with this code bound, one needs roughly T>=p^(2/5), hence L no larger than about
p^(3/5). This invalidates the near-critical cheap-box regime; it does not give a
lower bound for every possible selector or every ECDLP algorithm. [pcc:unverified]

## Outcome and successor

The new rank-two source has inexpensive offset decoding, but cheap selection
alone again leaves a serious generic-yield obstruction. Merely retaining b or
adding one fixed generator does not establish progress to a complete algorithm.
The mu=0 branch, higher support/degree, other height regimes, saturated ideals,
growing-rank families, infinity and other curve models remain outside this count.
No original branch or relation check is discarded. [pcc:unverified]

A successor must escape bounded-dimensional curve coding and account for search
cost and useful original yield together. A concrete next mathematics question is
whether a module with rank/support growing with log p admits an implicit short-row
search that avoids enumerating its whole small-anchor code. The competing outcome
is that its increased rank expands the support/height cost enough to remove the
benefit. Derive an explicit rank/weight/cost inequality before any implementation
or numerical launch. Existing numerical budget/runtime admission remains missing;
the earlier frozen Sage control is still unexecuted. [pcc:unverified]

## Next inequality to test, without a launch

For a growing-rank successor, record r=independent modular generators, N=full
coefficient support, s=small code coordinates sufficient to identify the model,
and log(T)=log(p/L). The generic-model information test is

    s*log(2T+1) >= 2*log(p) - log(number of admitted model transforms).

This is a necessary coverage diagnostic when such a code actually exists, not a
lower bound for every algorithm. Any explicit code enumeration pays the left-hand
information size. A proposed improvement must instead give a genuine implicit
search, prove that the selected integer row is nonzero/independent on the original
solution component, and charge its support, height and extraction costs. Merely
calling a sparse kernel routine does not provide those properties.
[pcc:unverified]
