# Prospective cubic-quotient shortcut discriminator

The first source direct004 check exits0: actual odd-cubic norm nonzero, tight
simple roots, exact signed curve zero locus, and unique u for a fixed v once
the selected support exceeds dU. No numerical curve/field control executed.

Next hypothesis: reducing u^2-c*g=f*v^2 modulo the fixed cubic f might compress
colored search into a constant-dimensional quotient. Necessary modular square
congruence alone is not expected to be sufficient: the quotient must itself
be a square polynomial with the required degree and selected signs.

Prediction/control: for any actual cubic f, set u=0 and g=-f*X. Then f divides
u^2-g, but no v can satisfy u^2-f*v^2=g because that would force v^2=X.
Odd degree should reject the latter over any field, without a numeric instance.
This is a symbolic relaxation counterexample, not a split/nonsingular colored
curve instance or an ECDLP lower bound. If it compiles, reject the bare quotient
test as a complete selector and retain the square-quotient obligation.

Acceptance: prove actual necessary congruence from the full norm factorization
and the promised symbolic false positive using maintained degree/cancellation
laws, standard axioms/default limits only. Raw direct005+ receipts retained.
Resources and all378 frozen pins/21 rows/earlier execution boundaries unchanged.
