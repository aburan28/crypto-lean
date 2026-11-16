# A known-target color checksum, and its representation budget

16 November 2026. This tests one concrete filter for the overlapping-support
selector proposed in PR21. It supplies four shared finite-group laws and
actual-point/checksum-group instances. It does not supply a new hidden-tuple
extractor, measured speed or complete subexponential ECDLP algorithm. No
native numerical, paid or qualification execution. PCC is unverified.

## A useful correction to the candidate interface

A coefficient checksum need not have an unknown target. Give every record
in color i the same weight lambda_i in an additive checksum group Q. Every
legal coefficient vector w containing one unit in each color satisfies

    H(w) = sum_i lambda_i = T,
    H(u)+H(v)=T whenever u+v=w.

Thus the target T is known without reading the hidden record choices or
private discrete-log labels. It can enforce a necessary compatibility
condition with no loss of legal final vectors. PR21's warning about an
UNKNOWN checksum target was conditional; this known-target construction
is a separate case. It is standard linear checksum algebra, not a novelty
claim. [pcc:unverified]

This observation creates a testable question: can the filter exploit the
full number of overlapping representations as distinct checksum chances?
The answer depends on their color profiles, not merely their count.

## Exact characterization and finite image

Let I be the finite color type, J the record-choice type, and G any
additive commutative group. Suppose weights lambda(i,j) satisfy

    exists T, forall c:I->J, sum_i lambda(i,c(i))=T.

If J has a supplied element j0, this is equivalent to

    forall i,j,k, lambda(i,j)=lambda(i,k).

For the forward direction, change one coordinate of an otherwise fixed
legal tuple. Delete that coordinate from both finite sums and cancel the
equal remainder. The converse sums one fixed weight per color. These are
the generic shared laws `weights_eq_of_common_target` and
`common_target_iff`; the actual prime-field point-subgroup probe applies
the latter unchanged. The common-target condition concerns ALL legal
coefficient tuples, not just tuples whose group sum is zero.
[pcc:unverified]

For a nonnegative partial coefficient array u, put d_i=sum_j u(i,j).
Existing natural scalar-sum distribution gives the shared law
`checksum_eq_profile`:

    H(u)=sum_i sum_j u(i,j) smul lambda_i
        =sum_i d_i smul lambda_i.

If a finite candidate family V has d_i<=K for each u in V and every i,
the exact shared endpoint `checksum_image_card_le` is

    card {H(u) : u in V} <= (K+1)^card(I).

Each image value comes from a profile I->Fin(K+1). The proof is inclusion
in that finite profile image, followed by existing image-cardinality and
function-cardinality laws. It does not assume random/independent checksum
outputs, distinct representations or a uniform selected-output law.
The same endpoint is instantiated at actual Weierstrass point subgroups
and ZMod q, including composite q. [pcc:unverified]

| Shared law | Kind / owner | Existing floor used |
|---|---|---|
| weights_eq_of_common_target | Generic law, Group.ColorChecksums | sum_erase_add, update_of_ne, cancellation |
| common_target_iff | Generic law, same owner | preceding law and sum_congr |
| checksum_eq_profile | Generic law, same owner | sum_nsmul_assoc |
| checksum_image_card_le | Generic law, same owner | finite subset/image card, card_fun/card_fin |
| Actual point / ZMod probes | Endpoints | unchanged shared laws, inherited group instances |

Full primitive arrays are the semantic inputs. Projecting them to profiles
is justified only for this checksum count; the selector still needs full
coefficients for legality, nonzero provenance and scalar recovery.

## Consequence for an overlapping-support filter

Fix a legal final w and its representation family BEFORE choosing a residue
alpha uniformly in a finite Q; weights are also fixed independently of
alpha. A representation passes a split filter when H(u)=alpha and
H(v)=T-alpha. By additivity the second condition follows from the first
for a valid representation. Its actual survival probability is therefore
the number of DISTINCT H(u) values divided by |Q|, at most

    min(1,(K+1)^m/|Q|),   m=card(I).

This is a hand probability reading of the exact finite image count.
Repeated representations in one profile do not create new residues.
It also holds when weights/families are formed from input point data
before the independent uniform residue is sampled. Letting weights depend
on that residue requires a different argument. [pcc:unverified]

PR21's sparse shape represents w=u+v with u binary, v ternary,
weight(v)=h, and a positive entries of v on w's selected coordinates.
It has hand count R=binom(m,a)*binom(m*b-m,h-a) and weight(u)=m+h-2a.
For h=O(m), choose K=m+h-2a=O(m). The profile image is at most
2^(O(m log(m+1))), even when R contains exponentially many record choices.
At balanced m about sqrt(log2 r), this is subexponential in log r. Taking
a modulus of size2^(Omega(log r)) solely because R is that large cannot
give constant survival under this independent-uniform-residue rule.
[pcc:unverified]

Several such additive checksums, combined into a vector group, still
factor through the SAME profile; their opportunities cannot be multiplied
as independent representation counts. This does not rule out smaller
moduli, choosing a particular profile deterministically, adaptive target
selection, nonlinear compatibility, joint point-coordinate filtering or
other representation shapes. It also does not assert that all group-zero
solutions have the universal target required by the characterization.
[pcc:unverified]

Controls: with b=1 the within-color condition has no choices to compare;
with m=0 the tuple sum is empty; K=0 permits only the zero profile. Some
weights collapse even more profiles, so the count is an upper bound rather
than a claimed uniform distribution. Arbitrary per-record weights can
distinguish more representations, but no common known target for every
legal tuple is then assumed.

## What changes in the selector search

The checksum is a valid compatibility layer with a known target. It does
not by itself justify hashing a huge overlapping family down by its full
representation count. The next joint interface must connect an efficiently
generated coefficient-compatible family to the actual elliptic group
zero condition, while retaining charged construction and recovery costs.
The previous interval-gcd block query is one proposed interface; its exact
cheap implicit implementation is still missing. Per-record filters that
preserve a group-zero constraint need an actual algebraic contract and
their own generation/yield analysis. [pcc:unverified]

Wagner's cited generic-group comparison explains why a provenance-only
filter followed by generic group matching cannot be advertised as a new
subexponential prime-order discrete-log algorithm. The scoped result here
is the finite profile image bound, not a new general lower bound.
The original complete end-to-end criterion remains unmet.

## Evidence and primary review

Prospective plan1209ad5 and inherited floor682c584 precede sourcea3c5a77.
Build003 and actual-point/ZMod assembly001 pass. Floor001's API-name/scalar
orientation errors and build001's missing finite-image equality instance
remain with original sources/logs. No mathematical hypothesis, proof limit,
trust, inventory or linter policy was weakened. Canonical gate001 audits
219 theorems with0 failures and0 trusted-native exceptions. All4 named
axiom prints use only propext, Classical.choice and Quot.sound. No fresh
checker or hosted pass is asserted.
[pcc:unverified]

KB tools unavailable; bounded fallback used PR21, the current shared
sources and exact Mathlib declarations. No novelty claim. Primary sources:

- [Li--Ye](https://arxiv.org/html/2610.10446), sections1.1--1.2: integer dot-product modular filters, distinct representation values, mixing and charged list generation. These contracts are separate from a color-constant checksum.
- [Randolph--Wegrzycki](https://arxiv.org/html/2511.10823), section2.1: representations, mixing and compatibility. No integer exponent is imported.
- [Wagner2002 author version](https://people.eecs.berkeley.edu/~daw/papers/genbday.html), sections2--3, Theorem2/Corollary1: efficient merging depends on group access/model. Its generic-group comparison is cited with that scope.

Six older owner claim subjects and consumer frozen histories stay intact.
PR21 landing/hosted-failure receipts and scoped autonomy/outcome accompany
this substantive study. No empirical values exist to plot or to add to
canonical measured performance graphs.
