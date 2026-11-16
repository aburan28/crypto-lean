# Known-target coefficient checksums: prospective plan

16 November 2026. Before any Lean edit of this family. The objective remains
a complete classical subexponential prime-field ECDLP algorithm. This is
a discriminating test of one overlapping-support interface, not a change
to the cost/yield targets. No native numerical, paid or qualification work.

## Question and predictions

For a one-per-color coefficient vector w, a checksum with one weight per
color has the known target sum of those weights. This corrects a possible
overgeneralization of PR21's conditional warning about an UNKNOWN checksum
target: some coefficient checksums do have a known target without losing
legal tuples. PR21's conditional statement stays intact.

Competing hypotheses:

- H1: such a known-target checksum can exploit the full overlapping
  representation count R as independently mixing hash values.
- H2: forcing a common target for every legal tuple makes an additive
  checksum constant within each color. Its value on a nonnegative partial
  vector depends only on color totals. With per-color total at most K,
  at most (K+1)^m values occur, irrespective of the record count b.

The smallest informative proof is the exact finite characterization and
image bound below. For a fixed legal w, a uniformly random residue in a
finite checksum group Q lands in its representation-value image with
probability at most min(1,(K+1)^m/|Q|). Thus using an exponentially large
modulus solely because R is exponentially large need not retain constant
probability. This is a hand probability/asymptotic reading of a finite
image bound, not a general overlapping-representation impossibility.

For PR21's sparse shape K=m+h-2a and h=O(m), the bound is
2^(O(m log(m+1))), while R may contain b^(h-a) choices. Several additive
known-target checksums collected as a vector still factor through the same
color profile. Small moduli, adaptive targets, nonlinear compatibility,
point-coordinate filters and joint generation remain outside this test.

Controls: b=1 has no within-color choice; m=0 is vacuous; K=0 has one
profile; constant weights attain a possibly smaller image; an arbitrary
per-record checksum is not assumed to have a known target.

## Six-field instance gate

1. Structure above: finite index types, finite sums in additive commutative
   groups, natural scalar action, finite image cardinality. Primitive
   coefficients are actual finite arrays of integers/naturals, equivalent
   to full finitely supported arrays here, rather than group-value proxies.
2. Existing laws as stated: Finset.sum_erase_add, Finset.sum_congr,
   Function.update_self/update_of_ne, additive cancellation,
   Finset.sum_nsmul_assoc, Finset.card_le_card/card_image_le, Fintype.card_fun
   and card_fin. Missing only the generic interfaces named below.
3. Objects: weights lambda:I->J->G; legal tuple c:I->J, checksum
   sum_i lambda(i,c(i)); nonnegative partial arrays u:I->J->Nat with
   checksum sum_i sum_j u(i,j) smul lambda(i). Nonempty J supplies a fixed
   tuple for the converse. Finset.image requires DecidableEq of the hash
   codomain, supplied classically at actual endpoints. No curve or
   uniform-group-output hypothesis.
4. Assembly floor: use existing finite-sum deletion/update and scalar-sum
   distribution laws directly, and finite image/function cardinality.
   Repeat additive-group/cancellation at an actual prime-field Weierstrass
   subgroup; formal final endpoints apply the new laws unchanged.
5. Missing components only: changing one coordinate forces equal weights;
   common-target iff within-color weights are constant; checksum factors
   through color totals; finite checksum image capped by (K+1)^card(I).
   All reusable laws belong in shared Group.ColorChecksums first.
6. Inheritance table:

| Operation | Inherited law | Glue |
|---|---|---|
| Compare two legal tuples | sum_erase_add, sum_congr, cancellation | change one coordinate |
| Constant color weights | finite sum congruence | common target endpoint |
| Sum coefficients per color | sum_nsmul_assoc | scalar-action factorization |
| Color-profile container | Pi of Fin(K+1), card_fun/card_fin | bounded total witnesses |
| Image cardinality | card_le_card, card_image_le | subset witness |
| Actual group instance | Mathlib point group, subgroup inherited operations | unchanged endpoint |

## Proof chain before code

Fix a default tuple. Replace its coordinate i by j or k. Both sums equal
the common target. Separate their i terms by sum_erase_add. Every erased
term agrees by update_of_ne. Cancel that common erased sum to obtain
lambda(i,j)=lambda(i,k). Conversely, within-color constancy makes every
tuple checksum the sum of one fixed weight per color.

For a natural partial array, move each color's sum across the existing
natural scalar action to obtain checksum=sum_i total_i smul lambda_i.
If all totals are at most K, form d:I->Fin(K+1) from those totals. Every
checksum value is the image of this d under profileHash. Inclusion in
the image of the whole finite profile type, followed by card_image_le and
card_fun/card_fin, gives the required cap. No presumed mixing or random
output model enters this argument.

One Lake process at a time. Preserve failed sources/logs, use fresh receipt
paths, no limit/trust/linter changes. Floor must pass before shared laws;
final actual-group assembly, canonical audit and all named axiom prints
remain required. All six older claims/subjects and consumer frozen histories
remain unchanged. Unrelated ProjectiveVeluInstanceProbe.lean stays untracked.

## Literature and scope before choosing the proof

KB tools unavailable (no loaded knowledge/theorem connector); bounded
fallback reviewed PR21 and current source declarations. Re-read Wagner2002
author sections2--3, especially Theorem2/Corollary1: generic group merging
alone does not supply a subexponential prime-order discrete logarithm.
This scope comparison is a cited input, not a new lower-bound theorem.

Read Li/Ye https://arxiv.org/html/2610.10446 sections1.1--1.2, especially
the primary integer dot-product filter, its mixing hypothesis and charged
filtered-list generation. Re-read Randolph/Wegrzycki
https://arxiv.org/html/2511.10823 section2.1: coefficient representations,
hashing and compatibility are separate obligations. No integer exponent
or all-representation mixing law transfers to a color-constant checksum.
No novelty claim. An initial web call used the wrong open-key schema;
corrected ref_id/lineno call succeeded, with no research execution.
