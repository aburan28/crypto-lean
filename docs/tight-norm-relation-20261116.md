# Tight norm rows now give actual elliptic-curve relations

A supplied nonzero tight interpolation row is connected to the actual Mathlib
point group and then to scalar recovery. The proof uses coordinate-ring ideals
and quotient dimensions, avoiding an additional assumed principal-divisor
oracle. Fast useful row discovery remains open; the complete classical
subexponential prime-field ECDLP criterion is unmet. [pcc:unverified]

## Exact endpoint and assumptions

Let W be a short Weierstrass model over a field K, with a1=a2=a3=0. For a
finite indexed family of nonsingular affine points P_i=(x_i,y_i), assume x is
injective and (u,v) is a nonzero polynomial pair satisfying

    u(x_i)+y_i*v(x_i)=0,
    degree(u^2-(X^3+a4*X+a6)*v^2) <= number of points.

The checked endpoint `short_tight_row_sum_zero` concludes SUM_i P_i=0 in
W.Point. The component-cap endpoint accepts2deg(u)<=t and3+2deg(v)<=t.
No principal-ideal equality, group sum, divisor oracle, odd subgroup condition
or characteristic-other-than2 condition is assumed by this bridge. Explicit
nonsingularity, distinct abscissas, nonzero pair and degree budget remain.
This does not cover repeated abscissas or points at infinity by omission.
[pcc:unverified]

## Coordinate-ring proof rather than a surrogate model

The function F=u*1+v*Y lives in W.CoordinateRing, Mathlib's actual quotient
K[X,Y]/(W). Its free basis over K[X] is1,Y. The basis shows that the nonzero
pair gives F!=0. Its actual algebra norm is the maintained short cubic norm.
[pcc:unverified]

Each row equation puts F in the actual ideal I_i=(X-x_i,Y-y_i). This is proved
by mapping the existing two-variable polynomial evaluation ideal into the
coordinate ring. Distinct x_i make the ideals pairwise coprime: subtracting
their X generators gives the nonzero scalar x_j-x_i, with an explicit inverse.
The product of the ideals is therefore their intersection. [pcc:unverified]

The existing norm-dimension theorem gives

    dim_K W.CoordinateRing/(F) = degree(Norm(F)).

The earlier maintained tight-root certificate proves this norm degree is
exactly t from the stated row equations and upper bound. The actual quotient
by each point ideal is K. Chinese remainders therefore give dimension t for
the quotient by their intersection. Containment yields a surjective linear
quotient map between equal finite dimensions; it is injective, so

    (F) = PRODUCT_i I_i.

For a nonempty index set the positive dimension supplies finite dimensionality;
the empty point-sum case is handled separately. No infinite-dimensional
finrank-zero inference is used. [pcc:unverified]

Mathlib's Point.toClass sends each P_i to the ideal class of I_i and is
injective. The product ideal is principal, so its class is1, and the actual
point sum is zero. The final row endpoint constructs the principal equality
internally; only an intermediate reusable lemma takes it as an input.
[pcc:unverified]

## Actual mixed labels and recovery

Let G have prime additive order q, H=k*G, and P_i=alpha_i*G+beta_i*H with
natural labels. The relation above implies q divides SUM_i(alpha_i+k*beta_i).
In the separate scalar field ZMod q, if SUM beta_i!=0, the checked formula is

    k = -SUM alpha_i / SUM beta_i.

The base field K and scalar modulus q are separate in the statement. The
unknown k occurs in the specification H=kG, not as an input needed to evaluate
the displayed label ratio. The nonzero denominator is an explicit condition,
not an established frequency or useful-yield theorem. [pcc:unverified]

The colored symbolic application takes a selected choice from an actual
mixed-point pool, restricts its globally injective abscissas, applies the row
caps and proves the same recovery formula. This is a certificate for a supplied
choice and row. It is not an implementation that discovers them. [pcc:unverified]

## Controls and scope

The horizontal three-point family with y=-1 and x=[r,s,-r-s] has row(1,1).
Given actual nonsingular points and injective abscissas, its group sum is now
checked to be zero. The previous cubic-adic report remains frozen as a record
of its earlier boundary; this successor supplies that conditional group bridge.
No original-subgroup frequency is inferred for the family. [pcc:unverified]

The empty-index control uses the nonzero unit function1 and yields the empty
point sum. The repeated-point control proves that a nonsingular point ideal is
not coprime to itself: its quotient is K, so it is proper. Thus replacing
injectivity by a multiset with duplicate point ideals would invalidate the
Chinese remainder step. [pcc:unverified]

Thirteen maintained laws, three actual symbolic controls/applications and one
colored mixed application compile. Owner-build001, actual002, mixed001 and
axioms001 have observed exit0; the application logs are empty. Thirteen named
axiom probes use only standard foundations. The canonical all-tracked audit
gate001 exits0:684/0/0, on source dd78a8350b504b716d3a71d99d235dd70be1af5e.
Its19 additions from665 are13 named owner laws,4 applications and2 generated
or maintained equations; no removals. Exact names are in audit-delta001.json.
No default-limit/trust/inventory/linter exception or custom axiom/native_decide.
Raw failed inputs and diagnostics are retained with durable status receipts;
source snapshots use .lean.txt so failed archival inputs are not maintained
Lean targets. [pcc:unverified]

Still open: a fast nonzero finder in the correct joint norm/colored model,
useful original yield including the nonzero denominator, and complete runtime
and asymptotic accounting. No measured speed or classical subexponential
ECDLP algorithm is claimed. The next research obligation is discovery or yield,
not another assumed norm-to-group bridge. The separate colorful-circuit and
list-decoding screen records translation folding as a prospective candidate,
with full-orbit cardinality and partial-orbit pole-cost tests still HAND.
[pcc:unverified]

No scientific/numerical/field/curve/Sage/LLL/native qualification, paid job,
image build/pull or earlier control execution occurred. The prospective control
remains UNEXECUTED. Unknown live shared charged/reserved remainder and missing
runtime/caller/capacity/custody admission remain;2USD proposal is not a grant or
balance. Existing hosted billing lock and disabled monitor after task-service
errors are separate from local source proofs. All494 older pins and24-row
history, frozen evidence and journal multiplicities are preserved. [pcc:unverified]
