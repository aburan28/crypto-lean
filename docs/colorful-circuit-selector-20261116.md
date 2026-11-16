# Discovery screen: colorful dependence and list decoding

This is a primary-literature screen and a new prospective direction, separate
from the checked tight-norm output bridge. No implementation, measured speed,
useful yield or subexponential ECDLP algorithm is established. The complete
criterion remains UNMET. No field/curve/numerical/control execution occurred.

## Does a matroid algorithm already supply the needed zero?

[Bárány and Onn, Colourful Linear Programming and Its Relatives, section5](https://www.renyi.hu/~barany/cikkek/69.pdf)
distinguish the two tasks explicitly. Theorem5.3 uses matroid intersection for
an independent colorful set. Theorem5.1 treats dependent colorful sets as
NP-complete over rational input. Thus an independence algorithm cannot be
substituted for the required singular-transversal finder. The rational
worst-case result is not a reduction for our finite-field elliptic row family
and is not an ECDLP lower bound.

[Eiben, Koana and Wahlström, Determinantal Sieving, TheoretiCS2025](https://theoretics.episciences.org/16626)
and the [full version, Theorems1.3,1.5,1.6](https://arxiv.org/html/2304.02091v3)
give sieves for monomials whose selected column submatrix is nonsingular.
The journal version does include general-field exterior-algebra variants;
characteristic2 alone is therefore not a reason to reject the paper. The
output mismatch remains: the selector needs a singular transversal. A proven,
efficient transformation to the required nonbasis predicate is still missing.

[Eiben, Koana and Wahlström, FPT algorithms over linear delta-matroids](https://arxiv.org/html/2502.13654v1)
extends this style of algebraic sieving to feasible supports in a linear
delta-matroid, represented by nonsingular skew-symmetric principal submatrices.
No representation of our desired dependent-transversal family as such feasible
sets was obtained in this screen. Generalizing the matrix format by itself is
not a conversion of the output predicate.

[Bérczi and Schwarcz, Rainbow and monochromatic circuits and cuts in binary matroids](https://arxiv.org/abs/2012.05037)
gives a rainbow-circuit/monochromatic-cut alternative for binary matroids.
Neither binary representability of the prime-field elliptic interpolation
matroid nor removal of the alternate cut outcome was established. Its theorem
therefore does not yet supply the proposed selector.

## A separate list-decoding candidate

[Zhang and Liu, Solving ECDLP via List Decoding, ePrint2018/795](https://eprint.iacr.org/2018/795)
does give an end-to-end ECDLP reduction through minimum-weight elliptic-code
words. The [paper, equation16 and conclusion](https://eprint.iacr.org/2018/795.pdf)
also analyzes the repeated calls needed because successful perturbations are
rare. The authors state that their resulting algorithm does not reach square
root time. A polynomial-time decoder call is consequently not a fast overall
selector. Replacing its success probability by a constant would erase the
bottleneck rather than solve it.

The direct PDF fetch returned403 (retained receipt); the browser's indexed
primary PDF text was inspected, including sections3.2 and4 and the conclusion.
No PDF download, implementation or independent numerical reproduction is
claimed. The prior decoding proposal remains useful as a concrete baseline.

[Cheng, Hard Problems of Algebraic Geometry Codes](https://arxiv.org/abs/cs/0507026)
uses randomized reductions for hardness of general elliptic AG-code minimum
distance/decoding with alphabet sizes exponential in block length. This does
not exclude better algorithms on our specific randomly generated pools.
[Li, Wan and Zhang](https://arxiv.org/abs/1501.01138) give a minimum-distance
formula when the evaluation set occupies at least two thirds of the curve
group. That large-set condition does not by itself supply a small evaluation
pool or a useful codeword finder.

## New candidate to test: translation-folded elliptic codes

Hypothesis: folding coordinates along a known curve automorphism may give
more decoding radius and improve the rare-success bottleneck. The standard
list-decoding paper itself distinguishes folded code families from its plain
elliptic-code instance. A transfer to the original elliptic group is required.

First discriminator (HAND, not yet a Lean theorem): if a nonempty finite
evaluation set is closed under translation by a point G of prime order q,
the orbit of any member contains q distinct points. Hence the evaluation set
has at least q members. Folding along that entire translation orbit cannot
produce a subexponential-size input in log(q). This only addresses a set
closed under translation by the full prime-order generator; it does not
exclude partial folds, other automorphisms, extension-field constructions or
all list-decoding methods.

Next independent source task: prove this actual group/orbit cardinality
obligation and inspect whether a proposed fold avoids full orbit closure while
retaining the decoder guarantee and original nonzero label yield. If it does,
derive its full success/runtime expression before any numerical proposal.
Do not re-use ordinary matroid intersection or nonsingular-support sieving as
a dependent selector without an explicit new reduction.
