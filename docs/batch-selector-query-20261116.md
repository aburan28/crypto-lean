# Arbitrary-subtotal retention and the batch-query contract

16 November 2026. This round removes the zero-subtotal restriction from the
finite two-gate interface, derives a separately scoped interval-intersection
estimate, and tests what a fast batch query must supply. It continues the
original classical subexponential prime-field ECDLP objective. No native
numerical case, benchmark, qualification run, paid job or speed measurement.
PCC standing remains unverified.

## Exact interface for a fixed arbitrary subtotal

For a finite additive commutative group G, an actual Finset S, and arbitrary
U,V,t, put W=U+V and

    C_W = {P in S | W-P in S} = S intersect (W-S).
    [U+t in S and V-t in S] iff [U+t in C_W].

Seven shared laws in Group.TranslatedIntersections supply this semantic
subset, its membership interface, the original acceptedCount reading and
the single-tag mean/variance. For raw uniform t, q(W)=|C_W|/|G| is exactly
the two-gate success probability; its indicator variance is q(W)(1-q(W)).
No zero-target or symmetry hypothesis is needed. Existing shifted-hit laws
are applied to C_W unchanged. For W=0 and S=-S, C_0=S recovers the previous
component. [pcc:unverified]

The actual prime-field final probe applies the original-count and moment
endpoints unchanged at Mathlib nonsingular Weierstrass point subgroups over
ZMod p. Finiteness comes from nonsingularPointEquiv, and NeZero p is derived
from primality. The same explicit DecidableEq dictionary is installed in
goal and proof contexts. No extra mathematical hypothesis or proxy group.
The older frozen ShiftRepresentations/ShiftMoments files stay unchanged.
[pcc:unverified]

For k independent uniform shifts, the standard raw binomial reading gives
E Y=kq(W), Var Y=kq(W)(1-q(W)) and no-survival probability (1-q(W))^k.
This round formally checks the actual original count and single-tag laws;
the displayed product-pool reading is hand application of the same existing
independent-indicator theorem, not a new full-pool Lean endpoint. Both child
tests depend on the same shift; their probabilities are not multiplied.
[pcc:unverified]

## Hand analytic estimate for a fixed coordinate interval

This paragraph uses a different, fixed interval gate, rather than asserting
a bound for every realization of the earlier random marker threshold.
Take a nonsingular short-Weierstrass E/Fp, p>3, and subgroup H of order r.
Let I be a cyclic field interval of length L, alpha=L/p, and

    S = {P in H excluding O | x(P) in I}.

For every W in H excluding O, the following hand bound follows from the
primary mixed character estimate and interval Fourier-L1 bound:

    abs(|C_W| - (r-2)*alpha^2)
       <= 8*sqrt(p)*(1+ln p)^2.                         (1)

This is an analytic application, not a formalized character-sum theorem in
the new module. The finite interface above is checked without this bound.
[pcc:unverified]

Derivation. Expand both interval indicators in additive field characters.
The sum runs over H excluding O,W. The both-trivial frequency contributes
(r-2)alpha^2. At a nonzero frequency pair (a,b), use

    f(P)=a*x(P)+b*x(W-P).

When a,b are both nonzero, f has distinct double poles at O,W and degree4.
They cannot cancel; pole order2, with p>3, also prevents Artin-Schreier
degeneracy. Kohel--Shparlinski Corollary1 bounds the subgroup sum by8sqrt(p).
With only one nonzero frequency, degree2 gives4sqrt(p); removing the other
excluded point adds at most1, still within8sqrt(p). Summing coefficient
absolute values, their interval Fourier-L1 estimate contributes at most
p^2(1+ln p)^2, cancelled by the Fourier p^-2 normalization. This proves (1)
at the stated hand scope. The case W=O is handled separately by symmetry,
using |S|=(r-1)alpha+error with absolute error at most4sqrt(p)(1+ln p).
[pcc:unverified]

A conservative useful specialization is b>=1, L=floor(p/b), p>=2b, r>=4 and

    r >= 128*b^2*sqrt(p)*(1+ln p)^2.

Then alpha>=1/(2b), the main term of (1) divided by r is at least1/(8b^2),
and its error is at most1/(16b^2). Thus q(W)>=1/(16b^2) for W!=O; the
separate single-gate bound gives the same conservative floor for W=O.
Taking k=16b^2 yields fixed-subtotal raw survival at least1-exp(-1).
All constants here are hand inequalities; no sampled evidence is used.
[pcc:unverified]

The subgroup-size condition matters. Do not assert this floor for arbitrary
tiny subgroups, or for every short random marker interval. With r comparable
to p and b=2^(O(sqrt(log r))), the displayed condition eventually holds.
Original-point or auxiliary cleanliness rejection needs a separate argument;
the formal single-tag model and the analytic count use their stated raw laws.
The result does not describe the joint distribution of an algorithm's
adaptively selected internal states.

## What the fixed-height cost does and does not decide

The earlier two-b^2-family, b-shift construction tests2b^3 states. That
operation count is larger than the direct four-color pair join's b^2
additions, but b^3 at a fixed height can still fit the proposed balanced
subexponential target. It is not by itself an asymptotic obstruction.
The relevant missing cost contract is growth through all m colors, including
compatible auxiliary tags, duplicates, retained states, failed attempts,
full provenance, witness recovery and final scalar checks. [pcc:unverified]

Here is a hand check of one explicit architecture. Take s independent
uniform color lists of size b, and a single fixed subset S of density delta,
independent of the lists. Consider ALL N_s=b^s original partial tuples whose
subtotal, plus a fixed shift, lies in S. Every subtotal is uniform, and the
subtotals of two distinct tuples are pairwise independent: condition on all
records except their two distinct entries in one differing color. Therefore

    E X_s = N_s*delta,
    Var X_s = N_s*delta*(1-delta),
    Pr[X_s < (E X_s)/2] <= 4/(N_s*delta).

The expected number of unordered equal-subtotal pairs retained in S is

    N_s*(N_s-1)*delta/(2*r).

Thus when N_s is of order sqrt(r) and delta is of order1/b, explicit complete
materialization has of order sqrt(r)/b states with high raw probability,
while equal-point deduplication has very few collisions. At m approximately
sqrt(log2 r), that state count still has logarithm n/2-O(sqrt(n)).
These are raw-input hand counts for a complete, whole-level, single-current-
filter materialization. They do not lower-bound lazy/selective/future-aware,
compressed, multi-filter or adaptive algorithms. Do not assume their output
law from matching support alone. [pcc:unverified]

## Concrete query idea: exact block decisions before expansion

The next proposed selector operation is an exact sparse-reporting oracle
on index blocks A of centers and B of shifts:

    empty(A,B,tau) iff no (a,j) in A x B satisfies
                         kappa(U_a+T_j) <= tau.

With a globally charged compact preprocessing phase and polylogarithmic
block-query cost, a binary partition/self-reduction could report K hits
using O((K+1)*log(N*M)) oracle calls, plus preprocessing, metadata and output
checks. Query cost must include every inspected entry. An oracle that
rescans both lists per call need not meet that total bound. A randomized
version would need explicit false-negative and false-positive work budgets.
This is a proposed interface, not an implemented oracle or time bound.

One algebraic candidate is to retain, implicitly, the finite-sum abscissa
polynomial

    R_AB(Z) = product_(a,j with U_a+T_j affine)
                         (Z-x(U_a+T_j)).

For an affine interval gate I, block nonemptiness is positive-degree gcd
with F_I(Z)=product_(z in I)(Z-z). Repeated roots retain raw pair multiplicity;
point-at-infinity hits, when the chosen gate includes O, need their separate
opposite-point dictionary query. Reconstructing an actual pair still needs
the block self-reduction and full primitive provenance. The representation
must remain implicit with charged updates and interval/gcd decisions: merely
writing this product does not give that capability. [pcc:unverified]

Explicit R_AB has degree |A||B|, and explicit F_I has degree about p/b.
Fast evaluation or modular composition does not make those coefficient
vectors free. A scalar interval-product/factorial algorithm likewise does
not automatically evaluate this arbitrary quotient-ring or compressed
elliptic block object cheaply. No such algorithm is supplied here.

## Primary review and what was actually imported

KB unavailable: no loaded knowledge/theorem tools; inherited wrapper is
unusable. Bounded fallback read the preserved204 interval/join assessments,
current C report and the following primary statements. No novelty claim.

| Primary source read | Interface checked | Implication for this task |
|---|---|---|
| [BGGKU theorem1.1](https://arxiv.org/html/2205.00342) and algorithm input | coefficient-vector polynomial, explicit evaluation points | applying it to every raw pair still supplies the grid |
| [ECFFT theorem7.2](https://arxiv.org/html/2107.08473) | circuit for a fixed supplied set; full evaluation table | auxiliary smooth-order curve does not change the target group or create a reporting oracle |
| [van der Hoeven/Lecerf introduction](https://www.texmacs.org/joris/kucomp/kucomp.html) | evaluation and modular composition input models | no sparse pair-output contract imported |
| [Warren theorems2/3](https://arxiv.org/html/2211.09465) | finite-field incidence bounds, irreducibility/size conditions | an incidence-count bound is not a reporting implementation |
| [Kohel--Shparlinski Theorem1/Corollary1/Lemma3](https://www.i2m.univ-amu.fr/perso/david.kohel/pub/character.pdf) | mixed subgroup sums and interval Fourier-L1 bound | hand application in (1), with pole/exceptional cases checked |
| [Bostan--Gaudry--Schost introduction, pp1777--1780](https://specfun.inria.fr/bostan/publications/BoGaSc07.pdf) | polynomial-coefficient recurrences and interval products | does not supply a polylogarithmic arbitrary block interval/gcd oracle |

The latest [modular-factorial preprint TR26-211](https://eccc.weizmann.ac.il/report/2026/211/)
was checked at primary abstract level only. Its stated special-divisor and
prime-density scope is not a general quotient-ring algorithm; the full
paper was not audited and no complexity claim is transferred here.
FLINT's current tree APIs were also read; its revised documentation flags
some LLM-generated prose, so theorem claims above rely on primary papers.
Kim--Tibouchi2019 conference section2 confirms the earlier Fourier setup;
it is not used to strengthen Kohel--Shparlinski's scope.

## Evidence and current acceptance

Prospective plan fdb4470 and inherited-law floor c62ae17 precede shared
source b4b9f52. The new module has7 named laws. Floor001's argument-order
and DecidableEq-context errors are retained with its original source/log;
floor002, focused build001 and actual-field assembly001 pass. Canonical
gate001 audits212 theorems with0 failures and0 trusted-native exceptions.
All7 named axiom prints use only propext, Classical.choice and Quot.sound.
No fresh lean4checker executable or hosted pass is asserted. No proof
limit, source inventory, trust or linter policy is changed. Raw warning
spaces remain; source/prose whitespace checks are separate. [pcc:unverified]

| Requested deliverable | Current scope |
|---|---|
| Move beyond zero-subtotal retention | Exact finite count and single-tag moments; actual prime-field assembly |
| Arbitrary-subtotal interval survival | Hand analytic estimate (1), explicit subgroup-size condition |
| Find a fast selector route | Block-decision/resultant proposal; required cost remains open |
| Check full state costs | Scoped raw whole-level count and collision budget; hand analysis |
| Complete end-to-end subexponential algorithm | Unmet: charged multilevel construction, witness extraction and actual useful-yield/recovery bound missing |

The existing original target remains T<=2^(C*m*log(m+1))*(m*b)^c*N^c and
theta>=2^(-C*m*log(m+1)) at balanced m,b, including all construction,
failures and scalar recovery. Nothing above establishes that contract.
The frozen numerical-panel checkpoint-access dependency is unchanged.

[Diagram](batch-selector-query-20261116/flow.svg) and inspected PDF separate
the exact interface, analytic application and missing query. No empirical
data exists to plot. Canonical measured scoreboards and older consumer
proposal diagrams have no new measured value/completed-algorithm edge to
change. Crypto4311/4338/4352 frozen histories/resolvers remain untouched;
the owner ledger and all four older claim subjects retain their prefixes
and bytes. PR19's queued autonomy/outcome records land with this substantive
change, without a recursive metadata-only PR chain.
