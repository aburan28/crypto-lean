# Cubic-adic roots are not a substitute for bounded full norms

The higher-precision square-root idea has two problems. Unconstrained roots
exist at every finite precision on the stated odd-subgroup inputs. Capping
the independently lifted root can instead lose a valid full norm row. The
correct bounded congruence retains both norm components and becomes exact
once its modulus degree exceeds the error bound. This is a representation
result; fast useful nonzero discovery remains open. [pcc:unverified]

## Constructive lifting with explicit inverse data

Over a commutative ring, suppose f^(n+1) divides u^2-g, with quotient a, and
f divides2u*w-1, with quotient b. The source checks the correction

    u' = u-f^(n+1)*w*a,
    u'^2-g = f^(n+2)*(-b*a+f^n*w^2*a^2).

The new root is unchanged modulo f. An inverse for2u0 modulo f therefore
transports through the initial residue class, and induction gives roots at
every positive power f^k. This does not assume a new inverse at each full
precision, an irreducible modulus or a square-root oracle. [pcc:unverified]

The unit assumptions are connected to the actual elliptic input. For a curve
record y^2=x^3+a*x+b with y!=0, define

    B(X)=(X^2+xX+x^2+a)/y^2.

The checked identity gives (x-X)B=1 modulo the cubic f=X^3+aX+b. Product
inverses are then explicit. The earlier square-residue witness and a target
inverse supply an inverse for2u0 when characteristic is other than2.
[pcc:unverified]

For actual Mathlib short-Weierstrass points killed by a common odd q, a
nonzero point cannot have double zero, hence its finite ordinate is nonzero.
The source supplies this point-to-unit bridge rather than assuming it.
All index multiplicities and point correlations remain. [pcc:unverified]

## All precisions still accept every tuple

For EVERY colored tuple of nonzero points in this regime and EVERY k>0,

    f^k divides U^2-product_i(C x_i-X)

has a witness U of degree strictly below3k. The bound is obtained by actual
polynomial remainder modulo the monic cubic power. The symbolic application
uses mixed points alpha_p*G+beta_p*H with qG=qH=0, without a hidden scalar or
independence assumption. [pcc:unverified]

If a standalone witness cap is d and3k<=d+1, every tuple still fits it.
At the usual cap d=floor(t/2), the checked mixed-input application gives
no rejection when6k<=t+2. This sufficient no-pruning range does not show that
larger k has useful yield or that its cap is necessary for the full norm.
The lifted U is a congruence witness, not the useful interpolation pair.
[pcc:unverified]

The negative unit control is generic: f=X,g=X,u0=0 passes modulo X but has
no square root modulo X^2 over any field. Thus the unit hypothesis cannot
be dropped from the universal lifting statement. Some other nonunit examples
may lift; the control does not classify them all. [pcc:unverified]

## A completeness issue with independently capped roots

The full equation is u^2-f*v^2=g. It yields u^2=g modulo f, but generally
not modulo f^k for the SAME u. A separately lifted root changes u. Placing
the original component's cap on that independent root is consequently a
new condition whose necessity has to be proved. [pcc:unverified]

The source provides a counterexample for every cubic parameter pair a,b:

    (u,v)=(1,1),  g=1-f.

This is an exact full norm pair, within the t=3 pole budget. It passes the
first congruence with root1, yet no polynomial U of degree at most2 can pass
modulo f^2. The error degree would be below6, forcing U^2=1-f, impossible
because the latter has odd degree3. For characteristic other than2, the
explicit lift U=1-f/2 has degree3 and passes modulo f^2. Its degree jump
and divisibility are checked in the actual symbolic applications.
[pcc:unverified]

This is also assembled with signed curve records. Put

    a=-(r^2+r*s+s^2), b=1+r*s*(r+s),
    x=[r,s,-(r+s)], y=-1.

All three records satisfy the curve equation and1+y=0. The norm is the
negative product of their three linear factors. Under distinct x's the
application composes the maintained tight signed zero-locus law, showing
that a valid tight row is lost by the independently capped lift. This is
a generic signed curve/norm-model family; no subgroup-yield frequency or
new group-zero-sum theorem for the family is claimed. [pcc:unverified]

A capped-root heuristic would require its own retained useful-yield argument.
It cannot simply inherit completeness from the full norm equation. This
does not exclude every use of degree-restricted reconstruction or every
selector. [pcc:unverified]

## The correct bounded finite-precision representation

Retain BOTH components:

    f^k divides u^2-f*v^2-g.

If2deg(u)<=t,3+2deg(v)<=t,deg(g)<=t and3k>t, the source proves that this
congruence is equivalent to the full polynomial norm equality. A nonzero
error would have degree at most t and at least3k, a contradiction. The zero
error branch is retained. The sufficient component-cap interface has t>=3;
the generic error-degree law supplies the more general formulation.
[pcc:unverified]

The horizontal row above passes this corrected test at k=2,t=3. This makes
the encoding exact for the bounded model; it supplies no fast nonzero
solver for the joint norm/colored system. Selected signs, monicity, original
zero/infinity branches and the final group/label checks remain required.
[pcc:unverified]

## Validation and remaining criterion

The maintained source has25 generic laws and5 symbolic applications.
Final owner-build001,actual003,mixed001,axioms001 exit0; both application
outputs are empty, and25 named axiom prints use standard dependencies.
Canonical all-tracked gate001 exits0:665/0/0. Its30 additions from635 are
25 owner laws and5 symbolic applications, with no generated equations or
removals. Source7e503fa predates and is unchanged throughout the audit.
No proof-limit/trust/inventory/linter
exception, custom axiom or native_decide. [pcc:unverified]

Raw induction-base, additive-group/constructor/proof-retention interfaces,
arrow/iff precedence and local-let unfolding failures remain with durable
exit receipts. The redundant tactic warning was removed before the final
owner build. Reproduction notes identify the edits without claiming that
the notes are raw failed-input snapshots. [pcc:unverified]

The next genuine algorithmic question is fast nonzero discovery in the
correct joint bounded norm/colored system, or a different approach. Actual
principal-divisor/pole/group-zero-sum and original mixed-label useful-yield
gaps remain. No measured speed, full classical subexponential prime-field
ECDLP algorithm or all-selector impossibility result is established.
[pcc:unverified]

All449 older pins/23 rows and frozen evidence are preserved. No scientific/
numerical/field/curve/Sage/LLL/native qualification, paid job, image build/pull
or control execution. Earlier control remains UNEXECUTED, with live cost and
actual runtime admission still missing. The disabled PR monitor/task-service
failure is tracked separately from the source results. [pcc:unverified]
