# Degree-two completions are centered pair-sum queries

Candidate B from crypto PR4338 now has an exact coordinate interface over
actual Weierstrass points. The shared source builds, and the final generic
and prime-field assembly passes. The canonical all-source gate audits169
theorems,0 failures,0 trusted-native exceptions. Signed PCC standing is
separate from these local source assertions.
[pcc:unverified]

## 1. Exact coordinate interface

For actual points P,Q,S on a Mathlib Weierstrass curve, use the existing
normalized representative key_S(P)=xRep(P-S), including infinity.
Mathlib's exact xRep fiber law and group cancellation give

    key_S(P)=key_S(Q) iff P=Q or P+Q=S+S.

Thus for P!=Q and S+S=T, the collision is equivalent to P+Q=T. These two
shared laws compose existing operations and theorems; they do not introduce
a new coordinate, replacement point group or projective chart. The actual
ZMod p assembly applies them unchanged and reads P+Q=-A as (P+Q)+A=0.
Both law axiom prints list only propext, Classical.choice and Quot.sound.
[pcc:unverified]

| Source declaration | Scope | Inherited laws |
|---|---|---|
| CryptoLean.CenteredCompletion.centered_xRep_eq_iff | Field F, DecidableEq F, actual W.Point | Point.xRep_eq_xRep_iff, sub_left_inj, neg_sub, sub_eq_sub_iff_add_eq_add |
| CryptoLean.CenteredCompletion.centered_completion_iff | same; P!=Q; S+S=T explicit | previous endpoint, or_iff_right |

The half-target hypothesis is explicit. On the consumer's odd prime-order
subgroup, S=[(r+1)/2]T satisfies it because [r]T=0. This uses a public scalar,
without access to the records' hidden scalar labels. Its O(log r) group
operation cost is hand accounting. Subgroup halving is not a newly formalized
law in this module. [pcc:unverified]

## 2. Relation to the proposal's pencil (hand bridge)

Let D be an anchor divisor of degree m-2, A=mO-D, and T=-sum(D). The
standard divisor-class identification gives A~2S whenever S+S=T. Choose h
with div(h)=A-2S. Multiplication by h identifies L(A) with L(2S):

    div(h*f)+2S = div(f)+A.

Translation identifies L(2S) with the span of 1 and x(P-S). A basis change
therefore identifies the extended degree-two pencil map with a projective
linear transform of key_S. Common factors cancel in the ratio; remove the
fixed zeros at the anchors and interpret poles/base-point extension through
the linear-system map. Raw 0/0 evaluation is not an admissible key.
[pcc:unverified]

This Riemann--Roch/divisor bridge is a written argument using the sources
below, not a newly checked Lean theorem. The source checks the exact centered
coordinate interface. The diagonal P=Q is a genuine extra fiber and must be
excluded; disjoint clean input colors supply that exclusion.

## 3. A fully charged explicit batch baseline

Build a dictionary from every pair of the last two colors:

    dictionary[R_i+S_j] contains the actual record pair (i,j).

Retain collisions/multiplicities as needed for final checks. For each chosen
anchor, compute T=-sum(D), query the dictionary, recover its records and
perform the actual relation, label and scalar checks. This replaces repeated
per-anchor pencil-key tables by one shared pair table. It does not search
the anchor family implicitly. [pcc:unverified]

| Phase | Hand charged cost |
|---|---|
| Pair table | b^2 group additions; O(b^2) records; point encoding and dictionary work |
| K arbitrary supplied anchors | O(K*m) group additions for explicit sums; K dictionary queries |
| Input and output | read all primitive inputs; retain provenance; decode and verify final outputs |
| Full anchor expansion | K=b^(m-2); no subexponential bound follows |

Hash dictionary costs are expected-data-structure costs with exact point
equality checks; sorting supplies a deterministic logarithmic-factor
alternative. No timing or implementation was measured. Computing the
centered key is unnecessary for this explicit baseline. Faster pencil-basis
updates alone do not remove the charged anchor search. [pcc:unverified]

## 4. Yield bound for a specific anchor schedule (hand analysis)

Let the original raw input consist of B0=mb independent uniform points in
the order-r subgroup. Permit an anchor family of at most K tuples chosen
from the first m-2 colors using only those inputs and independent coins.
The family must not depend on the last two colors. Conditional on that
prefix and those coins, each fixed remaining pair has uniform group sum.
If Z counts all anchor/pair completions with multiplicity, linearity gives

    E[Z] <= K*b^2/r.

No independence of different pair events or different anchor sums is needed.
Let C be the original point-only cleanliness event: reject infinity and
repeated abscissas. For Pr(C)>0,

    Pr(a completion exists | C) <= E[Z]/Pr(C)
                                <= K*b^2/(r*Pr(C)).

The exact coordinate fibers contain at most P and -P. The union bound for
raw samples gives Pr(C) >= 1-B0^2/r (one infinity event per record and at
most2/r per pair's x-collision). At the proposal's balanced growing
parameters B0=2^o(n), this lower bound tends to1. All of this probability,
conditioning and asymptotic accounting is hand analysis, separately scoped
from the two coordinate laws. [pcc:unverified]

If b=ceil(r^(1/m)), m=max(3,ceil(sqrt(n))), n=ceil(log2 r), and K=2^o(n),
the stated schedule has success at most2^(-n+o(n)). It cannot supply the
proposed2^(-O(m*log(m+1))) useful-output floor. This conclusion applies to
the specified family selection, not to future-aware/adaptive anchor
selection, implicit-family lifting or a different selector architecture.
It does not lower-bound general ECDLP algorithms. [pcc:unverified]

## 5. The constructive problem left by this assessment

The remaining B interface is now concrete: the two-color pair-sum target
set has a charged b^2 description. Given its points and the other m-2
colors, lift one target to its actual anchor records without expanding an
exponentially large family. A compressed representation must account for
every basis/key update, intermediate expansion and output lift. The fixed-
family yield bound does not rule out an algorithm that uses the last two
colors to construct its anchors. [pcc:unverified]

One route to examine is an exact compressed translation operator on the
pair-target predicate, closed under the remaining color lists. Its state
size, zero-test and witness extraction must be supplied; writing the
exponential product as an unevaluated expression is insufficient. This is
an unimplemented follow-on hypothesis, without a cost or novelty claim.

The complete-algorithm criterion remains unmet. Candidate A still needs a
capped nonzero product-system extractor; B still needs implicit anchor
lifting and useful-yield analysis; C's four-leaf provenance/moment check
remains an independent next attempt. No numerical/native/paid/qualification
execution was started, and no frozen panel or old conflicted evidence changed.

## 6. Source history and evidence

Prospective plan commitb3be549 precedes the first Lean edit. Floor001 first
exposed a missing DecidableEq F in the generic point-operation instance;
the original source/log are retained as text. Floor002 states the required
instance and passes before new source6ff00060599fe7b33d704cc0795f602f0e5d523d.
The first final assembly imported ZMod.Basic, which explicitly has no Field
structure; assembly001 source/log remain. Assembly002 imports the actual
Mathlib.Algebra.Field.ZMod instance and passes, without changing the source
laws or strengthening the mathematical assumptions. [pcc:unverified]

The plans, module, root import, probes, all original logs and final audit
material are under docs/receipts/centered-completion-20261115/ and
docs/receipts/CenteredCompletion20261115/. Lean4.35.0, Mathlib
cfc55fc58714a59dc06e6e79edc6d1d95140d3c2. No proof limit or trust policy
was changed. No fresh lean4checker pass is asserted. [pcc:unverified]

Final gate001 compiles every tracked source, including both new valid-path
probes, and audits169/0/0. The source module remains6ff0006; generic/actual
assembly is committed at7bc6d4c. The existing gate tool and trust manifest
are unchanged from the prior owner component. [pcc:unverified]

## Sources

KB unavailable in this runtime; no loaded connector and the inherited wrapper
failure is unchanged. Read the frozen candidate-B plan, exact current
Mathlib affine-point declarations, and these primary references:

- [Ben Lynn, Zeroes and Poles](https://crypto.stanford.edu/pbc/notes/elliptic/divisor.html): x-divisors and the degree/sum criterion for principal divisors.
- [Andrew Snowden, Lecture2](https://websites.umich.edu/asnowden/teaching/2013/679/L02.html): Riemann--Roch, Pic0 and the dimension/basis of L(2O).
- [Cheng, Hard Problems of Algebraic Geometry Codes](https://arxiv.org/html/cs/0507026), section2: the existing elliptic-code framework and positive-degree spaces. No worst-case hardness statement is transferred to the distribution-specific cost question.

The diagrams describe this interface and the unimplemented lifting step;
they introduce no measured data. Earlier measured canonical charts and the
frozen proposal PDF are unchanged.
