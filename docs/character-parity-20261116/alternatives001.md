# Fresh selector mechanisms: working trials

16 November 2026. User requested new ideas. Working hypotheses and hand
calculations, not a completed algorithm or a publication claim. No native
numerical benchmark, qualification or paid job. Existing claims, frozen
inputs and consumer evidence histories are untouched. The original complete
classical subexponential prime-field ECDLP criterion is unchanged.

The research-kb tools are unavailable in this session. Bounded fallback:
current selector reports, PKM2016 and APS2018 primary manuscripts already
on disk, and primary generalized-Jacobian papers downloaded below. No
literature novelty claim.

## 1. Carry-aware joins in a generalized Jacobian

This is a different source of structure from an additive coefficient hash.
Use the established generalized Jacobian extension for a modulus (M)+(N):

    (P,a) + (Q,b) = (P+Q, a*b*c(P,Q)).

Use Galbraith--Smith's convention c(P,Q)=f(P,Q)(M)/f(P,Q)(N), where
div(f(P,Q))=(P+Q)+(O)-(P)-(Q). Away from poles, f=v_(P+Q)/ell_(P,Q), so

    c(P,Q)=h(P+Q) * ell_(P,Q)(N)/ell_(P,Q)(M),
    h(R)=v_R(M)/v_R(N).

The opposite line/vertical convention in some sources inverts this
cocycle; do not mix them. Exceptional points require the published chart
patches, not an assumption that division is always defined.

### A normalized lift that uses no hidden labels

Let H have known prime order r with gcd(r,p-1)=1. The extension restricted
to H has a kernel F_p^*. Pick e with e*(p-1)=1 mod r and put s=e*(p-1).
For any lift j(P), define sigma(P)=[s]j(P). Multiplication by s kills the
kernel and projects to P. In the abelian extension sigma is independent of
the chosen lift and is additive. Its order divides r. The group-law
computation uses O(log(r*(p-1))) additions in this explicit extension.
It is not a map into F_p^*, and does not invoke a finite-field DLP.
Write sigma(P)=(P,a(P)). This is a working application of the coprime-order
extension laws; a formal actual-instance proof is pending.

Set F(R)=a(R)/h(R) on a valid chart. Then the lift law gives

    F(P+Q)=a(P)*a(Q)*ell_(P,Q)(N)/ell_(P,Q)(M).

Consequently the EXACT VALUE gate F(P+Q)=t becomes

    a(P)*a(Q)*ell_(P,Q)(N)-t*ell_(P,Q)(M)=0.

Let v_P=(x_P,y_P,1). Line evaluation is the determinant det(v_P,v_Q,v_T).
The last expression is therefore bilinear in the six-coordinate records

    Phi(P)=(a(P)*x_P,a(P)*y_P,a(P),x_P,y_P,1).

This is the concrete new join interface to test: field-coordinate carry
becomes a fixed-dimensional point/hyperplane incidence for each t. The
formula is a hand derivation from the published law, not an independent
formal or numerical result. Coincident points/tangents, inverses, infinity
and chart poles need separate handling.

### What would make it a selector

1. Construct a target family T of useful density and bounded description.
   An exact value t is not automatically a set of density1/b. No distribution
   for a(P), F(P) or their point-dependent images is assumed.
2. Batch these incidences on implicit partial sums with charged construction,
   output/provenance recovery and a known worst-case cap.
3. Derive useful survival for a full original relation, including how any
   representations or chart choices are generated. Root telescoping alone
   does not force every internal gate to pass.

A possible variant uses quadratic-character gates in several moduli, or a
multiplicative subgroup gate when the field supplies one. These avoid an
unknown coefficient-checksum target, but they do NOT turn into a single
cheap exact-value incidence: a large target set must not be enumerated for
free. The next smallest mathematical trial is the actual distribution and
fiber degree of F, followed by an output-sensitive carry-incidence routine.
Reject the simple route if it only gives ordinary explicit pair testing or
small exact fibers with too little yield.

### Existing security comparison

Galbraith--Smith Proposition2.1/Corollary2.2 and section3 explain the links
between prime-order DLPs in an extension, its base and its kernel. In
particular, a multiplicative kernel is not a generic reduction of ECDLP to
finite-field DLP. Their Remark3.4 identifies the usual embedding-degree/
pairing issue. The proposed use here is a carry-aware search interface,
not a claim that the extension itself breaks the DLP.

## 2. Small-root search with balanced projective intermediate sums

Use an interval factor base as a NEW end-to-end construction family; do
not silently replace the original iid colored-list law. For m points with
x_i in [0,B), use m-2 intermediate abscissas z_i and m-1 Semaev S3
constraints ending at the target abscissa. All actual points/signs and the
final scalar would be checked separately.

In affine integer representatives the intermediate z_i can be as large
as p. A straightforward lattice contains shifts of these modular equations
and p-powers. A sufficient short-vector certificate for g is

    ||g(B*X,p*Z)||_2 < p^t/sqrt(number of monomials),

when g vanishes modulo p^t on the root. This is the usual Cauchy--Schwarz
integer-vanishing test, not a claim that a suitable short polynomial exists.

First hand trial: an internal S3(z_i,x,z_(i+1)) row contains
z_i^2*z_(i+1)^2 with unit coefficient; its scaled norm is at least p^4.
At the ends, terms x^2*z^2 have weight B^2*p^2. Thus the unshifted t=1
rows cannot themselves satisfy the p threshold. Merely presenting the
addition chain as quadratic equations does not give a small-root attack.

The fresh modification is to represent each z as U/V modulo p with
balanced U,V of order sqrt(p), using rational reconstruction, and
homogenize S3. Its two full intermediate slots then have weight about p^2
instead of p^4; an end row has weight about B^2*p instead of B^2*p^2.
This improves the weighted-height budget, while doubling the intermediate
variables. It is not enough for the t=1 certificate; a mixed-equation
shift lattice must obtain independent integer relations. Constants,
zero denominators and the exact bounded-lift guarantee remain to check.

Next discriminating trial: derive the determinant and independence budget
for shifts of the HOMOGENIZED path system, before any LLL run. Include all
new numerator/denominator variables. Reject a bound that silently treats
unknown intermediate coordinates as small affine integers or treats
multiple short polynomials as algebraically independent.

This candidate attacks root extraction by arithmetic height, not by
materializing an implicit product grid. It currently has no useful-yield
or capped root-extraction bound.

## 3. Joint lifting through low-degree fiber towers

PKM2016 supplies factor bases from a composition of low-degree maps,
including a smooth-order isogeny chain on an auxiliary elliptic curve over
the SAME prime field. The auxiliary curve need not be isogenous to the
target curve. Its construction and subgroup/fiber cardinality are charged.

Try a dedicated solver that lifts the auxiliary-map fibers and the target
addition equations together, retaining exact common factors at each lift,
rather than expanding the full degree-B constraint or taking a generic
Groebner basis as the algorithm.

The proposed state is a triangular correspondence at one tower level:
remaining addition constraints plus the next low-degree fiber maps.
Branch on the next fiber only after a gcd/elimination condition is known
to be nontrivial. The key observable is the TOTAL degree/number of live
correspondences at every frontier, including failed branches. Low degree
of a single step does not bound this total.

Next discriminating trial: write the first two lifts for a two-color
addition equation and compute its exact elimination degrees in terms of
the per-step map degrees. Check whether projection to the next frontier
really prunes before lifting all leaves. Then test three colors. A rule
requiring all B^m tuples is rejected. A surviving rule needs a cap and
actual useful-yield analysis at growing m, and a full relation/recovery
cost including auxiliary-curve construction.

## Primary reading and access

- Petit--Kosters--Messeng2016, local
  /workspace/scratch/cover-transfer-literature/PKM2016.txt, sections3.1--3.5
  and5. This is prior art for the tower construction and the open dedicated
  root-finding interface, not a new factor-base claim.
- Amadori--Pintore--Sala2018, local APS2018.txt, introduction and the existing
  single-relation setting. Its asymptotic solver burden is not removed by
  asking for only one relation.
- Dechene, On the security of generalized Jacobian cryptosystems,
  https://cacr.uwaterloo.ca/techreports/2006/cacr2006-35.pdf,
  saved under sources/Dechene-security.pdf and .txt. Read explicit law and
  prime-order/security discussion. Arithmetic ePrint2006/033 formula was
  also inspected through indexed primary material; do not conflate its
  line/vertical convention with Galbraith--Smith's inverse convention.
- Galbraith--Smith, Discrete logarithms in generalized Jacobians,
  https://arxiv.org/abs/math/0610073, full four-page paper downloaded and
  read under sources/Galbraith-Smith.pdf and .txt.
- Primary ePrint2017/609 access403 and Diem old URL404; use the already
  preserved APS manuscript instead. Coppersmith EC-generator search found
  attacks using leaked coordinate bits; that leakage is not available here,
  so no bound is imported from its abstract.

## Current decision

Prioritize candidate1's normalized torus carry and bilinear incidence:
it gives a precise new coordinate-dependent join to examine. Candidate2
has an explicit improved height budget but no successful root certificate.
Candidate3 is a separate structured-input construction and solver trial.
All are research hypotheses; none meets the complete algorithm criterion.
No new PCC, benchmark, PR or frozen-evidence edit is warranted yet.

## Follow-through: simplify the carry to a quadratic-character join

Choose N=-M. The multiplicative carry has a direct expression that does
not need a generalized-Jacobian implementation. Write A=(a,b), and let
ell be a nonvertical chord/tangent through P,Q,R=-(P+Q). The standard
Weierstrass intersection polynomial gives the exact product identity

    ell(A)*ell(-A)=(x(P)-a)*(x(Q)-a)*(x(R)-a).

With kappa_A(P)=chi(x(P)-a), and with all three factors nonzero,

    kappa_A(P+Q)
      =kappa_A(P)*kappa_A(Q)*chi(ell(A)*ell(-A)).

The cubic polynomial identity also holds with root multiplicities for
tangents. Vertical lines/infinity and zero factors require their explicit
cases. The character is symmetric under P->-P. This is a hand application
of the existing line/negation/addition laws, not a new group-homomorphism
claim. It produces a precise simultaneous Legendre-symbol join rather
than an unknown additive-checksum target.

For several A_j, use all kappa_Aj(P)=+1 as a candidate gate. Its output
join condition consists of k low-degree chord-carry predicates. The next
algorithmic test is to find these sparse simultaneous matches without
enumerating every pair. Per-pair Legendre evaluation alone supplies no
batch improvement. Finite-field incidence COUNTS are not reporting
algorithms; real-plane Hopcroft bounds do not transfer automatically.

### Prospective six-field gate for the first symbolic assembly probe

1. Structure: Mathlib WeierstrassCurve.Affine over an arbitrary field,
   its actual Equation, negY, slope, addX and line/addition polynomials.
2. Laws as stated: Affine.addPolynomial_slope, C_addPolynomial,
   equation_iff/Equation and polynomial evaluation homomorphisms. Use the
   existing cubic factorization, not another curve-specific proof.
3. Object: evaluate the EXISTING factorization at an actual curve point A;
   the reflected ordinate is W.negY a b. This works before restricting to
   short Weierstrass or ZMod p.
4. Assembly: combine the existing norm/product identity with the existing
   root factorization via evaluation. Compile this floor endpoint before
   any new shared law or character theorem. No finite numerical case.
5. Missing: only evaluation/restructuring glue; generalized-Jacobian lift,
   density/yield theorem and batch reporting remain unimplemented.
6. Inheritance: point equation from W.Equation; reflected point from negY;
   chord and third abscissa from slope/addX; product roots from
   addPolynomial_slope; norm at A from C_addPolynomial; ring normalization
   only for sign/reordering. No trust, proof-limit or linter changes.

Assembly001 stopped on the unenabled bivariate type notation F[X][Y],
before its algebraic application. Original source/log preserved. Use the
existing explicit Polynomial(Polynomial F) type in assembly002; no
mathematical hypothesis or theorem statement changes.

Assembly002 reaches the existing factorization and norm law, but the
constant-embedding evaluation lemma is not a default simp rule. Preserve
source/log and explicitly use Polynomial.evalEval_C in assembly003, plus
the existing negY expression for final sign normalization. No new law or
curve hypothesis is introduced.

Assembly003 passes. It applies Mathlib's EXISTING nonvertical
addPolynomial_slope and C_addPolynomial laws at an actual Equation point,
for an arbitrary Weierstrass field/model, including tangents permitted by
that law. This is a local inherited-law assembly only; no all-source audit,
character theorem, density law or selector performance is claimed.

### Concrete inversion-free version of the new join

For distinct abscissas, let

    D_A(P,Q)=det((x(P),y(P),1),(x(Q),y(Q),1),(a,b,1)).

The normalized line evaluation differs from D_A by the secant denominator.
The two evaluations at A,-A have a SQUARED common denominator. It disappears
under the quadratic character. Thus the carry can be evaluated as

    C_A(P,Q)=chi(D_A(P,Q)*D_(-A)(P,Q)),

with no field inversion. With precomputed input bit-vectors kappa(P), the
gate kappa(P+Q)=(+1,...,+1) is equivalent, on the stated nonzero chart, to

    C_Aj(P,Q)=kappa_Aj(P)*kappa_Aj(Q) for all j.

This provides a precise NEW batching target: report a pair passing k
quadratic-character predicates on products of two bilinear determinants,
using actual point inputs and full output provenance. The polynomial
radicands have small bilinear descriptions. Taking their character does
not preserve a claimed low matrix rank; no such claim is made.

An explicit pair loop is only the control. A candidate batch routine must
state its preprocessing, block-query and witness-recovery costs and keep
its actual useful yield. Character sum/incidence bounds alone do not give
that routine. The input law and final original coefficient contract stay
unchanged for this candidate, unlike the new structured factor-base
families in candidates2/3.

Additional bounded literature search: finite-field incidence results found
are counting bounds; Hopcroft algorithms found use real-plane geometry.
No finite-field reporting complexity was imported from either. This leaves
the batched simultaneous Legendre-symbol join as an explicit research
subproblem, not an assumed oracle.
