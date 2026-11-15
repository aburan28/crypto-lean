# Norm chart laws

Consumer: crypto/research/shared_norm_algebraic_20261115/chart-pruning.md.
The original goal is an executable prime-field ECDLP algorithm with a sufficient
subexponential cost/yield contract; these supporting polynomial laws do not
supply that algorithm or a Groebner construction bound.

The six-field instance gate:

1. Structure above: Mathlib `Polynomial K` over a field, `Separable`,
   `Squarefree`, divisibility and `IsRelPrime` / `IsCoprime`.
2. Existing laws: `Polynomial.separable_X_pow_sub_C`,
   `Polynomial.Separable.of_dvd`, `Polynomial.Separable.mul`,
   `Polynomial.separable_X_sub_C`, `Polynomial.Separable.squarefree`,
   `Squarefree.squarefree_of_dvd`, `Squarefree.dvd_pow_iff_dvd`, and
   `isRelPrime_iff_isCoprime`. No shared norm cancellation law existed in
   the pinned library, so it is built here generically.
3. Object: a divisor U of X^d-c, c and d nonzero in K, separated from r,
   with A^2-f B^2=(X-r)U. No curve model is assumed or redefined.
4. Assembly probe: separability of U and (X-r)U from actual membership,
   nonzero evaluation and the existing laws type-checked under the pinned
   Mathlib/toolchain before writing the missing generic law.
5. Missing component supplied: `isRelPrime_of_squarefree_norm` on
   polynomials over any field. `kummer_norm_charts` applies it to the
   actual membership/target hypotheses; no squarefreeness or coprimality
   conclusion is assumed in that endpoint.
6. Inheritance: field/polynomial laws from Mathlib; shared norm cancellation
   here; retained circuit divisibility and coefficient-chart instance work
   belong in consumers. No consumer copies the generic proof.

One opening: the generic law uses the `Squarefree` predicate's common-square
factor contract and the `IsRelPrime` common-divisor contract. A common divisor
D of U and B is squarefree, divides A^2 and hence A. Then D^2 divides the norm,
so squarefreeness of that norm forces D to be a unit. No curve, quotient
scheme or syntax definition is opened.

The scope is exactly separability and coprimality. Degree-bounded Bezout witness
coordinates, membership-chain assembly, scheme equivalence, runtime, useful
relation yield and any ECDLP theorem are not formalized by these declarations.
Pins are inherited unchanged from lake-manifest.json and lean-toolchain.
