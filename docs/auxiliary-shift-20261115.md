# Auxiliary representations with a marker-rank filter

Study started 15 November 2026; continued 16 November. Candidate C of the
fast-selector proposals. This round constructs a finite random-threshold
filter, checks its compatible-representation count, and separates retention
from state-generation cost. No numerical/timing experiment, native case,
qualification or paid job was run. Statements below remain PCC-unverified.

## Constructive rule and finite survival endpoint

Let G be a finite additive commutative group of order r. Fix U,V with U+V=0.
Choose a negation-invariant key kappa:G->K into a linear order. Draw b>0
independent uniform markers M_i and an independent b-point shift pool T_j.
Use the cached threshold tau=min_i kappa(M_i). Accept a compatible tag j
when BOTH kappa(U+T_j)<=tau and kappa(V-T_j)<=tau. The shared source proves
[pcc:unverified]

    r^(2*b) <= 2 * Nat.card {raw pools // some compatible tag passes both}.

Thus the hand reading under independent raw uniform sampling is survival
probability at least1/2 for this fixed valid original relation. No coordinate
equidistribution, distinct sampled keys or absence of ties is assumed.
The shared Lean endpoint is the exact finite count, with actual tags, not
an asymptotic estimate. [pcc:unverified]

The proof uses the analysis equivalence

    swap_U(M,T) = (U+T, -U+M).

After swapping, the adjusted pool is M and the marker pool is U+T. Success
becomes the reverse comparison of the same two minima. Totality covers
every raw pool state by success or its swap preimage; the preimage has the
same cardinality by the existing subtype equivalence. Applying the existing
union bound gives the endpoint. Ties can lie in both events and are retained.
The swap is not a sampler, replacement primitive input or closing-witness
generator. Every raw array, including repeated entries, remains a separate
sample state; the finite image used to compute a minimum does not deduplicate
the pool space. [pcc:unverified]

For actual nonsingular Weierstrass points over ZMod p, p prime, use

    kappa_p(P) = p * (P.xRep 1).val + (P.xRep 0).val.

Mathlib's normalized xRep includes infinity, and xRep_neg gives key symmetry.
The final probe applies the unchanged endpoint to any subgroup H of this
actual point group. Finiteness is inherited through nonsingularPointEquiv;
NeZero p is derived from primality. No proxy curve/group or additional
mathematical hypothesis is introduced. [pcc:unverified]

## Actual primitive provenance and fixed-filter moments

For four original primitive records, put U=X1+X2 and V=X3+X4. On the actual
Finsupp coefficient space (Fin4 sum Fin k)->0 R over a nontrivial ring, set

    left_j  = e0+e1+f_j,       right_l = e2+e3-f_l,
    W       = e0+e1+e2+e3.
    left_j+right_l-W = f_j-f_l.
    left_j+right_l = W iff j=l; both W and the full sum are nonzero.

These are shared source laws. Same-tag joins cancel auxiliary provenance
and keep the original colored relation. A cross-tag actual zero relation
with a nonzero residual could be a different, larger DLP relation including
auxiliary records. It is not a formal-zero identity, but requires its own
output contract, charged construction and recovery/yield analysis. A planted
local T-T with full coefficient vector zero is inadmissible. [pcc:unverified]

For a fixed symmetric filter S=-S and raw independent uniform T:Fin k->G,
the actual count is

    Y(T)=card {j | U+T_j in S and V-T_j in S}, delta=|S|/r.
    E Y    = k*delta,
    Var Y  = k*delta*(1-delta),
    E Y^2  = k*delta+k*(k-1)*delta^2.

The subtraction k-1 is in R, so k=0 needs no unstated guard. Both gates
agree because V-T_j=-(U+T_j); their probabilities are not multiplied.
The sample law in the statements is exactly Measure.pi of uniformOn univ.
The proof rewrites the original acceptedCount once to real indicators and
uses integral_fintype, the translation sum equivalence, integral_comp_eval,
variance_sum_pi and variance_eq_sub as stated. The actual prime-field
assembly applies all three endpoints unchanged. [pcc:unverified]

If later conditioning on auxiliary cleanliness or another rejection rule,
the raw independence law cannot be reused without a separate conditioning
argument. Markers are independent selector coins. Public uniform scalar
multiples of a subgroup generator provide a mathematical uniform sampler
when the exact order is supplied, but its implementation, scalar sampling,
O(b log r) group-operation budget and any rejection cost are separately
charged. No private original scalar labels are read by this rule.

## Hand selectivity analysis, separate from the checked survival law

A symmetric constant key satisfies the survival theorem while retaining
everything. The survival endpoint alone therefore makes no density claim.
If every key fiber has size at most2, exchangeability and a finite tie count
give the following hand bound for the random threshold filter density:

    1/(b+1) <= E_M[delta(M)] <= 1/(b+1) + b/r.

For n=b+1 iid keys, let h be the number of entries attaining the weak
minimum. Then 1<=h<=1+the number of colliding unordered pairs. All n positions
are exchangeable, and a pair collides with probability at most2/r; divide
the expectation bound by n. This treats finite-field ties explicitly and
does not import continuous-CDF order-statistic formulas. [pcc:unverified]

For the actual normalized key above, infinity has key1 and affine points
have key p+x.val>=p; p>=2 separates them. Equality among affine keys gives
equal abscissas, whose actual curve fibers contain at most2 points. This
fiber argument and the density bound are hand analysis in this round;
the formal prime-field probe checks key symmetry and the survival endpoint,
not this selectivity proof. Do not label the latter Lean-verified.
[pcc:unverified]

## Charged explicit construction and next missing interface

For four supplied lists of size b, form all b^2 left pair subtotals and
all b^2 right pair subtotals. Generate b markers and b shifts; compute
the marker minimum once. Explicitly filtering every pair subtotal against
every shift takes 2*b^3 translated-point/key tests in this architecture.
Store surviving states with the full original indices and auxiliary tag;
join equal tags and opposite actual points, then check provenance and the
original relation. Include encoding, dictionary work, duplicates and output
recovery. Streaming and materializing have different storage costs, but
neither erases those raw tests. These are hand operation counts, not
measurements or lower bounds for other architectures. [pcc:unverified]

The ordinary explicit four-color pair join needs O(b^2) group additions
and a dictionary/sort join, plus encoding and output checks. The present
explicit shifted construction has no measured or derived speed gain over
that control. For fixed sampled markers, the moment endpoints price the
random compatible count; they do not generate the retained states cheaply.
[pcc:unverified]

The next constructive interface is a **coordinate-aware batch translated
filter query**: given centers U_a, a raw shift list T_j and threshold tau,
report actual pairs (a,j) with kappa(U_a+T_j)<=tau, with charged setup,
query work, memory, output and provenance. A fast method must avoid testing
every raw pair and justify its actual random-input yield. No such method
or runtime bound is supplied here. Global zero makes the two root children
opposite; it does not make every internal partial sum zero. Do not multiply
the one-join half-survival bound across a deeper tree without new contracts.

## Evidence and acceptance map

| Requirement | Evidence / status |
|---|---|
| New fast-selector mechanism | Marker minimum plus independent auxiliary shifts; constructed rule |
| Preserve full primitive coefficients | 11 ShiftRepresentations laws; same-tag cancellation explicit |
| Actual compatible-count moments | 7 ShiftMoments laws; fixed symmetric S and raw product-uniform law |
| Finite marker-rank survival including ties | 10 RankThreshold laws; positive b, exact raw cardinality |
| Actual general-prime-field assembly | Final probes use actual Mathlib points/subgroups, normalized key and inherited finiteness |
| Efficient implicit state generation | Open batch translated-filter query; explicit construction tests O(b^3) states |
| Complete end-to-end algorithm | Unmet: full selector construction, deeper-tree contracts, actual useful yield and label recovery/cost remain |

Source commit a078981171458959ef935ba33d5222e1eaa0dbf6 contains all28 named
laws. Prospective plans/floors precede both families: C ce238cc/a0f668a
and marker-rank50f5f2f/8fcb310. Pre-source PCC102ac7 and PCC9ea735 remain
unverified and pinned byte-for-byte. Canonical gate001 audits205 theorems,
0 failures and0 trusted-native exceptions, including every tracked source
and final probe. Explicit axiom output for all28 new named laws uses only
subsets of propext, Classical.choice and Quot.sound. All three final PDF
pages were rendered and inspected. No fresh lean4checker executable is
available; no fresh-checker or hosted pass is inferred.
[pcc:unverified]

The final target remains the proposal's charged bound, at m approximately
sqrt(log2 r), b=ceil(r^(1/m)): T<=2^(C*m*log(m+1))*(m*b)^c*N^c and useful
yield theta>=2^(-C*m*log(m+1)) for fixed C,c, including construction, failures,
extraction, decoding and final scalar checks. These are targets, not results.
The frozen numerical-panel checkpoint-access requirement is unchanged.

Failure evidence retains original floor001--003, moment-floor001/002,
moment-build001 and API/diagnostic001/002 sources/logs. No proof limit,
trust policy, source inventory or linter was weakened. Compiler-warning
trailing spaces are preserved as raw evidence; full archival diff checks
may report them even when source-only checks pass. Local source checks and
signed PCC standing retain different scopes. [pcc:unverified]

## Sources and graph scope

KB unavailable in this runtime; no loaded connector or usable wrapper.
Bounded fallback review used the frozen A/B/C proposal, earlier coordinate
join assessments and current pinned Mathlib sources. No novelty claim.

- [Wagner, A Generalized Birthday Problem](https://people.eecs.berkeley.edu/~daw/papers/genbday.html), author paper sections2--3: explicit scalar/XOR/subgroup filters; these do not supply coordinate-aware batch generation.
- [Howgrave-Graham/Joux, EUROCRYPT2010 slides](https://www.iacr.org/conferences/eurocrypt2010/talks/knapsacks.pdf), slides9--14: overlapping representations with explicit modular constraints; no historical exponent transferred here.
- [Yen-Chi Chen, Lecture9: Order statistics](https://faculty.washington.edu/yenchic/20A_stat512/Lec9_Order.html): the continuous-input density formulas assume almost-sure distinctness; finite ties are handled separately here.
- Mathlib cfc55fc58714a59dc06e6e79edc6d1d95140d3c2: Finset.Max, Logic.Equiv.Prod, SetTheory.Cardinal.Finite, Probability.UniformOn, Probability.Moments.Variance, MeasureTheory.Integral.Pi/Bochner.SumMeasure and Affine.Point.

BCJ's full-paper mirror was inaccessible; a Chicago search hit did not
contain the sought order-statistic section. Neither supplied an imported
algorithm/bound. All read-source limits remain explicit in the plans.

[flow.svg](auxiliary-shift-20261115/flow.svg) and its editable DOT describe
the proof and unresolved construction, with no timing chart because none
was measured. The inspected PDF uses the same diagram. Canonical measured
scoreboards and the consumer proposal diagram have no new measured value
or completed-algorithm edge from this component and remain unchanged.
Crypto4311/4338/4352 frozen branches and their separate resolvers remain
untouched. The owner ledger keeps main as a byte/parsed prefix.

The consumer IDC1 schema encodes polynomial expression identities, not
finite-event cardinality or these group-provenance statements. No surrogate
polynomial-evaluation certificate is asserted; the shared Lean sources and
explicit axiom receipts carry the formal component. No native evaluation
was run to manufacture an inapplicable certificate.
