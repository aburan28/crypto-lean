# Fixed-slope secant fibre count

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
