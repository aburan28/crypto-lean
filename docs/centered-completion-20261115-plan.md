# Candidate B: prospective centered-completion gate

2026-11-15, before the first Lean edit of this component. Continue the user's
fast-selector objective through candidate B in crypto PR4338's frozen plan.
The complete-algorithm criterion is retained. No numerical, native, paid or
qualification execution is planned. PR4352's pending merge-status review and
the frozen4311/4338 histories remain untouched.

## Six-field instance statement

1. Structure above: Mathlib WeierstrassCurve.Affine F, its actual nonsingular
   Point additive commutative group, subtraction and normalized xRep :
   Point -> Fin2 -> F. The codomain includes the infinity representative.
2. Theorem used as stated: WeierstrassCurve.Affine.Point.xRep_eq_xRep_iff,
   which says equal representatives iff P=Q or P=-Q. Also existing
   subtraction cancellation, neg_sub, sub_eq_sub_iff_add_eq_add. The only
   desired shared endpoint composes these laws after the translation P->P-S.
3. Object as instance: the centered map is existing xRep composed with
   translation by -S, on actual curve points. Target T and center S carry
   the explicit hypothesis S+S=T. No new point type or replacement curve.
4. Assembly probe: type-check the inherited xRep law at translated generic
   curve points, the generic group rewrite, and the identical translated
   xRep law over ZMod p with Fact p.Prime. The final probe applies the
   shared completion endpoint unchanged at these actual prime-field points.
   No subgroup or half-existence conclusion is hidden in the field instance.
5. Missing components only: the small shared centered-collision endpoint
   and its off-diagonal/explicit-target reading. Degree-two Riemann--Roch,
   the basis-to-centered-x identification, public subgroup halving, finite
   probability accounting and an implicit-anchor extractor retain separate
   hand scopes; none is asserted as part of this Lean module.
6. Inheritance table:

| Operation | Inherited source | New work |
|---|---|---|
| Points and group operations | Mathlib Affine.Point AddCommGroup | none |
| Infinity-aware x representative | Mathlib Point.xRep | none |
| Exact x fibers | Point.xRep_eq_xRep_iff | none |
| Centered input | existing subtraction P-S | composition only |
| Equal translated points | subtraction cancellation | none |
| Opposite translated points | neg_sub, sub_eq_sub_iff_add_eq_add | none |
| Off-diagonal completion | previous endpoint plus P != Q, S+S=T | shared endpoint |

## Proof chain before code

1. xRep(P-S)=xRep(Q-S)
   iff P-S=Q-S or P-S=-(Q-S), by the existing exact x-fiber law.
2. First disjunct iff P=Q, by subtraction cancellation.
3. Second disjunct iff P-S=S-Q, by neg_sub.
4. This iff P+Q=S+S, by sub_eq_sub_iff_add_eq_add.
5. Under P!=Q and S+S=T, the result iff P+Q=T.

No existing operation is opened or reimplemented. No custom axiom, sorry,
native_decide, limit override or duplicated curve proof. The first probe
is committed with its original log before adding the new shared source.
The final module and actual-instance probe will be built, every new law's
axioms printed, and the unchanged all-tracked-source audit run once.
Keep the unrelated ProjectiveVeluInstanceProbe.lean out of commits.

## Hand interpretation and next discriminating question

For anchor divisor D of degree m-2, write A=mO-D and T=-sum(D). On the
odd-order subgroup S=T/2 is obtained by the public inverse-of-two scalar.
The standard divisor-class and Riemann--Roch argument identifies A~2S;
after a common function factor and basis change, its degree-two pencil is
a projective transform of x(P-S). The base-point extension and that function-
space bridge are not newly formalized. The source law checks only the exact
centered-coordinate collision interface.

The next cost question is whether a compressed family can lift a point in
the two-color pair-sum set to its m-2 anchor records without expanding all
anchors. Precomputing all b^2 pair sums is a charged explicit baseline;
faster basis updates alone do not account for the anchor search. Bounds
for fixed anchor families must state independence from the last two colors;
they do not automatically cover future-aware/adaptive anchor selection.

## Sources checked before the approach

KB unavailable: no loaded connector; inherited wrapper failure unchanged.
Read frozen candidate B and current Mathlib Affine/Point.lean xRep section,
especially xRep_eq_xRep_iff at the pinned Mathlib cfc55fc58714a59dc06e6e79edc6d1d95140d3c2.
Read Ben Lynn's primary divisor notes (sum criterion and x-divisor),
https://crypto.stanford.edu/pbc/notes/elliptic/divisor.html , and Andrew
Snowden's primary lecture2 (Riemann--Roch, Pic0 and L(2O)),
https://websites.umich.edu/asnowden/teaching/2013/679/L02.html . Cheng
https://arxiv.org/html/cs/0507026 section2 supplies the prior elliptic-code
context and positive-degree dimension statement. No novelty or general
algorithmic lower bound is claimed.
