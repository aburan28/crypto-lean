# Universal shift pool: prospective density and adaptive retention

16 November 2026. Mathematical and Lean compiler work only. No numerical
curve cases, native evaluations, benchmarks, paid jobs or qualification.
Preserve all nine old PCC rows and 76 subjects. The unrelated untracked
ProjectiveVeluInstanceProbe.lean is outside this work.

## Question and discriminating result

Can polynomially many known scalar shifts simultaneously retain a two-gate
split for every pair of points, so later adaptive choices need no selected-
output uniformity assumption? Prediction: yes under an explicit joint-density
condition. This is a retention statement. It does not locate the original
hidden tuple, supply useful nonzero coefficients, or cap implicit extraction.

Let H be a prime-order r subgroup of E(Fp), p>3. Choose k nonzero anchors
with distinct abscissas, with 2k<r. Define kappa_j(O)=1 and otherwise
kappa_j(P)=chi(x(P)-x(T_j)); D is the simultaneous +1 set. For nonzero W,
the odd branch supports of f_I(P) f_J(W-P) cannot all cancel: both supports
sum to zero, whereas reflection through W changes their sum by n W for
0<n<=2k<r. Candidate hand estimates are

    abs(card D-r/2^k) <= k sqrt(p)+2k,
    abs(card(D intersect(W-D))-r/4^k) <= 2k sqrt(p)+4k (W!=0).

Treat W=0 separately using D=-D, and k=0 trivially. Remove the whole set
of anchor zeros and their W-translates before expanding indicators: an
ordinary zero and a modified Kummer-character value can differ at canceled
even zeros. The correction is at most 4k after normalized expansion.

If r >= 2*4^k*(2k sqrt(p)+4k), every ordered pair has at least
r/(2*4^k) good shifts. Q independent uniform shifts then have simultaneous
failure at most r^2 exp(-Q/(2*4^k)); the proposed cap is
Q >= 2*4^k*(2 ln r+ln(1/epsilon)). Charge all Q known scalar multiples,
all actual pair-specific gate scans, and the failure probability. No claim
that this pool can itself be exhaustively certified in subexponential time.

## Literature and inherited floor before edits

KB MCP tools remain unavailable; the previous wrapper attempt is recorded
in the predecessor study. Bounded exact Mathlib/owner search and primary
papers replace it; no novelty claim. Kohel--Shparlinski character.pdf,
section2 propositions1/2 and section3 unramified Lang-isogeny character
construction, provide the mixed-character framework. Its additive theorem1
is NOT a multiplicative theorem. Perret, Acta Arithmetica59(1991), pp284--288,
propositions3.1/3.3/4.3/4.5 and corollary4.6, give the tame conductor,
modified local values, and square-root bound. Primary scanned pages were
visually read, including the hypotheses excluding constants times powers.
The ramified quadratic character remains geometrically nonconstant after
an unramified subgroup-character twist. No blanket nonconstant-implies-
regular rule is used. Full source PDFs and reviewed sections will be indexed.

Sources:
- https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf
- https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/59/3/107098/multiplicative-character-sums-and-kummer-coverings
- Mathlib Logic.Equiv.Basic, Data.Fintype.Card/BigOperators,
  Algebra.BigOperators.Group.Finset.Basic, GroupTheory.OrderOfElement.
- CryptoLean.Group.TranslatedIntersections.both_gates_iff and its raw
  mean/variance; these laws are applied unchanged, never re-proved.

## Six instance fields

1. Structures: AddCommGroup, finite supports with sums, element additive
   order; finite tag types, function types, Finset events and their cards.
2. Existing laws: Finset.sum_image/sum_sub_distrib/sum_const;
   addOrderOf_dvd_iff_nsmul_eq_zero and Nat.le_of_dvd;
   Equiv.subtypePiEquivPi, Fintype.card_congr/card_fun,
   Fintype.card_subtype_compl, Finset.card_biUnion_le/sum_le_sum.
3. Objects: actual branch supports are Finsets in the existing point
   subgroup. Pools are Fin Q -> H, not new syntax or a certificate language.
   Bad events are pools missing one of a finite family of good tag sets.
4. Assembly probes: first compile the named inherited sum, order, product
   and union-count interfaces with abstract components. Then instantiate
   the generic owners at actual Weierstrass points/subgroups and actual
   completionFilter gate predicates. No custom analytic axiom.
5. Missing glue only: reflected-support sum and centered/order obstruction;
   fixed-event product miss count, finite universal miss bound and existence
   when that bound is strictly below the total number of pools. These are
   generic laws in CryptoLean.Group.TranslatedSupports and
   CryptoLean.Combinatorics.UniversalPools. Character sums, real exponential
   cap, and extraction consequences remain hand arguments, labeled as such.
6. Inheritance table:

| Operation | Existing law | New glue |
|---|---|---|
| Reflect a finite support | sum_image, sum_sub_distrib | sum equality |
| Exclude complete cancellation | element-order divisibility | centered-support consequence |
| Count pools missing a fixed set | subtypePiEquivPi, card_fun, card_subtype_compl | equality assembly |
| Bound any miss | card_biUnion_le, sum_le_sum | universal event endpoint |
| Exist a pool | finite card-complement/nonempty laws | strict-count endpoint |
| Actual two-gate predicates | both_gates_iff | unchanged application |

## Proof chains and controls

Reflected sum = sum over T of (W-P), by injective image; distribute sum;
constant sum minus sum T = card(T) smul W - sum T. Centering forces this
multiple to zero. Its order divides card(T); positive card(T) smaller than
the order contradicts Nat.le_of_dvd. No prime-field-specific group proof.

Fixed miss pools are equivalent to Q functions into the complement of the
good tag set; cardinality is (r-card(good))^Q. The union over demanded
events has size at most the sum of fixed miss sizes. If every good size is
at least a, this is at most number(events)*(r-a)^Q. If strictly below r^Q,
some pool misses no event. The r^2-pair and exponential versions read this
finite statement through standard real arithmetic; no analytic theorem is
introduced as a Lean hypothesis disguised as a proven character estimate.

Controls: empty family, empty good set, Q=0, repeated tags allowed,
zero subtotal, k=0, centered empty support, torsion equality at the order,
subgroup too small for the density condition, canceled even zeros. A good
global pool covers all pairs and therefore any adaptive subsequence; merely
covering a prechosen sequence is not the same statement.

One Lake process at a time. Preserve every failed source/log. Commit all
new Lean sources before the canonical all-tracked-source gate; inspect
every new named axiom print. Report, editable visual, PDF with all pages
inspected, scoped unverified PCC claim, ready PR and actual-head CI evidence.
No trust/limit/inventory/linter changes. Follow with an extraction mechanism,
not a repetition of this retention bound.
