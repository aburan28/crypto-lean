# Fixed-slope secant fibre count

Source867527c752375f21d47c000044d8215d07e432ba passes build003 and the
canonical repository-wide source/axiom gate:141theorems,0failures,0trusted
native exceptions. The seven new declarations use only standard foundations.
Exact source hashes, all three builds, source inventory and full gate logs are
retained under docs/receipts/line-incidence-20261115/. Hosted CI is separate.

The endpoint `CryptoLean.LineIncidence.slope_family_point_card` counts actual
affine point pairs satisfying the existing Weierstrass Equation. It bounds
the distinct-abscissa partners of a known curve point for a finite family of
slopes by twice the family's cardinality. The hypotheses are a finite field
and a known curve point; nonsingularity is unnecessary for this upper bound.
The consumer's probability/conditioning/cost consequences remain hand
arguments at their stated independence assumptions.

Prospective consumer scope crypto b1e8ecdd26, following checked partite
coverage. Sources checked before implementation: Wagner2002 full author
version sections2--3 and the ROS subsection4; Sutherland MIT18.783 Spring2013
Lecture2 section2.1.2. KB unavailable in the consumer runtime. Existing Mathlib
Affine.Formula.addPolynomial/addPolynomial_eq and Cubic degree/root-cardinality
laws are reused, rather than constructing a new curve model or cubic engine.

Target: over an existing finite field and Weierstrass curve, a prescribed
nonvertical line through a known curve point has at most two other affine
points with distinct abscissa. The actual Equation and addPolynomial semantics
are used. No curve nonsingularity is needed for this upper bound.

The consumer will apply the finite fibre count to independent uniform subgroup
points and point-independent slope sets, then separately charge conditioning
on global clean-base rejection. This source target is not the complete
probability/cost argument and constructs no relation selector. Adaptive slopes
and other partial joins are outside the consumer's proposed assessment.

Preserve first failures, source pins and canonical all-source/axiom receipts.
No proof limits, native_decide, custom axioms or numerical cases.

Build001 at ea59988 checks the polynomial degree/evaluation/root equivalence
and both x-fibre cardinalities, then fails on a tactic term with no expected
type at the final injection-bound composition. Give that existing inequality
its expected type through le_trans. No statement or hypothesis changes.
Build002 at af774d6 passes all six targets. Extend the endpoint to an actual
finite slope family's union with the existing card_biUnion_le law; no
probability/cost assumption is added to the curve theorem.
Build003/canonical proofgate001 pass at867527c. No numerical case was run,
statement weakened, proof limit changed or native computation trusted.
