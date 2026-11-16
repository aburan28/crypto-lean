# Tight norm interpolation as a selector acceptance certificate

The new direction is to search for a nonzero tight interpolation function,
with an acceptance certificate that excludes paired-point padding. This is
independent of the earlier scalar offset-window refinement. It does not yet
supply a fast colored nonzero extractor or a complete classical subexponential
prime-field ECDLP algorithm. [pcc:unverified]

## Actual source and certificate

Over any Field K define f=X^3+a*X+b and N=u^2-f*v^2 using actual univariate
polynomials. For every nonzero pair (u,v), N is nonzero: a zero norm with
v!=0 would equate degrees2deg(u)=3+2deg(v), which have opposite parity.
The v=0 and zero-pair cases are handled explicitly. This is formal polynomial
nonvanishing, not a point-function independence claim. [pcc:unverified]

For selected records (x_i,y_i) on y^2=x^3+a*x+b satisfying
u(x_i)+y_i*v(x_i)=0, the norm vanishes at every selected x. If the selected
x's are distinct and natDegree N<=t, where t is the support size, the source
proves all of the following. [pcc:unverified]

- N has exactly those t roots, each with multiplicity one, and degree t.
- There is no common K-valued zero of u and v anywhere. A common zero would
  give a repeated factor of N, contradicting the simple root multiset.
- At every selected record v(x_i)!=0 and y_i=-u(x_i)/v(x_i).
- On the actual affine curve, u(z)+w*v(z)=0 holds exactly at the selected
  signed records. For characteristic other than2 and y_i!=0, the opposite
  sign is excluded. A selected2-torsion ordinate y_i=0 is retained.
- N=C(leadingCoeff N)*product_(selected x)(X-x).

These endpoints include actual indexed and colored primitive-record
applications, not only an unconstrained replacement coefficient map.
The generic cap interface2natDegree(u)<=t and3+2natDegree(v)<=t supplies the
norm-degree premise. That sufficient cap interface requires t>=3; the direct
norm-degree certificate itself also retains the empty/small boundaries.
[pcc:unverified]

## Padding controls and the earlier kernel-state argument

A pure nodal row(g,0) for t selected nodes has norm g^2 of degree2t. For
t>0 it fails the tight degree<=t test. The duplicate-coordinate control is
important: two copies of the same actual curve record permit u=X-r,v=0
with norm degree2 and support size2. Distinct x's cannot be dropped.
Empty support retains the nonzero constant pair(1,0); the zero pair is
excluded by an explicit hypothesis. No random or numeric case was run.
[pcc:unverified]

The maintained InterpolationKernels exact-state injectivity proof uses a
pure u nodal witness when t<=dU. In the tight positive regime2dU<=t we
instead have dU<t. The new source proves that a pure u kernel row is then
zero, and two bounded kernel rows with the same v have the same u. Thus
projection to v is injective on each selected bounded kernel in this range.
This corrects the scope of the prior witness argument; it neither proves
that different supports now share kernels nor supplies a cheap lifting or
state-compression algorithm. [pcc:unverified]

## A shortcut tested and rejected

The tight factorization implies the necessary cubic congruence

    f divides u^2-C(leadingCoeff N)*product_(selected x)(X-x).

Reducing modulo the fixed degree3 cubic would be attractive for search, but
the quotient must itself be the square polynomial v^2. The source gives a
generic false positive for the bare divisibility relaxation: u=0,g=-f*X
passes f|(u^2-g), while N(0,v)=g would force v^2=X, impossible by degree
parity. This is a symbolic relaxation counterexample, not a claim that g
is a split colored curve instance. Bare cubic congruence is rejected as a
complete selector; square quotient and selected signs remain obligations.
[pcc:unverified]

## Remaining algorithmic bridge (HAND)

For t>=3 the usual pole-budget basis has2dU<=t and2dV+3<=t and t
coefficients: dU=h,dV=h-1 when t=2h+1; dU=h,dV=h-2 when t=2h>=4.
For a supplied colored choice this gives a square evaluation system.
Constructing it and finding a nonzero kernel row by Gaussian elimination
has a hand O(t^3) field-operation budget. This does not bound the number
of colored choices examined or implement a fast extractor. Exhaustive
b^t choice enumeration is still an available expensive baseline.
[pcc:unverified]

Using the earlier exact color-product constraints, a supplied nonzero tight
solution would select at least one zero factor in each color. Under global
x injectivity, t colors already give t distinct roots; the new degree
certificate leaves room for exactly one per color. This is a written
corollary of the maintained choice equivalence and new fixed-choice source,
not an additional compiled uniqueness endpoint in this phase. Finding that
nonzero solution with controlled cost and useful original yield remains open.
[pcc:unverified]

On a smooth projective short Weierstrass curve in characteristic>3, the
standard principal-divisor/pole-order argument should convert this exact
signed zero divisor into a point-sum relation. That geometric bridge and
multiplicity/pole identification are HAND here, not newly formalized in
Mathlib point-group semantics. Even after a checked group relation, the
mixed-label denominator in the subgroup scalar field must be nonzero for
ECDLP recovery. Its modulus need not equal the curve base-field modulus.
No group relation, useful yield or subexponential cost has been demonstrated.
[pcc:unverified]

One further HAND search refinement is to normalize the tight norm before
searching. Its leading term comes from u^2 when t is even, and from -f*v^2
when t is odd; those degrees cannot tie. Divide u and v by the nonzero
leading coefficient of the dominant polynomial. The proposed complete
normal forms are then N=product(X-x_i) for even t and
N=-product(X-x_i) for odd t. The dominant polynomial is monic, leaving
t-1 coefficient parameters in the usual pole-budget basis. This removes
an arbitrary scalar parameter in coefficient enumeration; it does not
reduce b^t colored-choice enumeration by itself. This leading-coefficient
normalization and a fast normalized polynomial-Pell solver are next proof/
algorithm obligations, not compiled claims or measured search improvements.
[pcc:unverified]

## Validation and evidence boundary

The final maintained source has24 generic laws and5 symbolic applications.
Owner-build001,actual001,axioms001 exit0; actual output is empty. Twenty-four
named axiom prints use only standard dependencies. Canonical all-tracked
gate001 exits0:597/0/0. Its31 additions from566 are24 owner laws,5 symbolic
applications and2 generated defining equations, with no removals.
No limit/trust/inventory/linter
exception, custom axiom or native_decide was introduced. [pcc:unverified]

Raw direct001 records an infrastructure exit127 before compilation: the
restored session PATH omitted the existing /home/agent/.elan/bin. The same
installed Lean4.35 was used after correcting PATH. Direct002 records interface
errors in power-zero, max-degree and singleton-count normalization plus a
DecidableEq statement binder; direct003/004/005 pass. All raw failures remain.
Inherited Mathlib module-format import warnings remain unchanged.
[pcc:unverified]

A broad static whitespace scan first stopped at the unchanged intentional
tools/selftest/fail/BuildError.lean fixture. The receipt retains that finding;
all new owner source/prose have zero findings. Full archival diff-check exit2
retains old raw whitespace, without changing the fixture, any frozen bytes,
proof inventory or linter settings. [pcc:unverified]

The earlier first-endpoint Sage control remains UNEXECUTED,1PythonAST/1JSON
parse only. No scientific/numerical/field/curve/Sage/LLL/native qualification,
paid/image build/pull/job/control execution occurred. Live shared charged and
reserved remainder and actual runtime/image/caller/capacity/custody admission
remain missing; the2USD proposal is not a grant or balance. All378 older
pins/21 ledger rows and frozen evidence remain preserved. [pcc:unverified]
