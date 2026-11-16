# Strict lift rigidity for the exceptional primitive branch

16 November2026. The complete classical subexponential prime-field ECDLP criterion
remains unmet. This package supplies a conditional obstruction for the declared
one-generator primitive selector. Eighteen generic laws and four symbolic source
applications compile; the full all-tracked audit is recorded separately.
[pcc:unverified]

## Exact theorem and its assumptions

Let G0=A2 W F1-A1 F2 be the frozen primitive, of chart profile(3,2).
The source anchors of lambda*G0 translated by tau,sigma are lambda,-2lambda*tau,
lambda*(tau+sigma). With their integer lifts lambda,c,d and Delta=2lambda, use
rational offsets -c/Delta and(2d+c)/Delta, assuming Delta!=0. Define the integer
polynomial in x,y,w,U,V,X,W

    S = G0(a,0,x,y,w, Delta*U-c*V, Delta*V,
                         Delta*X+(2d+c)*W, Delta*W).

The compiled scaling law gives S=Delta^5 times that rationally translated raw
primitive. The source applications connect the actual extracted anchors to the
clearing equations; they also check signed denominators and the zero polynomial
in the remaining coordinate. [pcc:unverified]

For an integer row f, coefficientwise divisibility by p of
lambda*S-Delta^5*f plus the STRICT coefficient bound

    |lambda|*|S_m|+|Delta|^5*|f_m| < p

forces literal equality Delta^5*f=lambda*S. This is a generic integer-polynomial
theorem; it does not assume a successful lattice search. A generic boundary
control shows that a nonzero multiple of p of magnitude exactly p prevents
replacing < by <=. The row-family witness theorem also derives cross divisibility
from explicit pA+cF/pB+dF expressions. [pcc:unverified]

Suppose a is centered, |x|,|y|<=B, |U|,|V|<=H1, and the exceptional congruences

    a+x²+xy+y² = 0 mod p;
    Delta*U+(Delta*(x+y)-c)*V = 0 mod p

hold. Compiled bounds6B²<p and(|Delta|*(1+2B)+|c|)*H1<p force BOTH congruences
to be literal integer equalities. The first also forces |a|<=3B². On this exact
branch S is identically zero for every remaining X,W. The actual seven-variable
composition theorem therefore yields f(x,y,w,U,V,X,W)=0 under the declared cross
bounds and Delta!=0. No original F2 equation or exceptional branch is discarded.
All divisibilities and strict bounds remain explicit premises of the final law.
[pcc:unverified]

## Audited hand coefficient bound — not newly formalized

Use unweighted coefficient l1 mass in the seven indeterminates and choose M>=1
bounding |a|,|Delta|,|c|,|d|. The shifted coordinates Zs,Vs,Ts,Ws have masses at
most2M,M,4M,M. The raw sums A1,A2 have masses4M,7M². With b=0, direct triangle
and product inequalities give

    mass(F1) <=16M²+16M³+4M⁴ <=36M⁴;
    mass(F2) <=144M⁴+72M⁵+9M⁶ <=225M⁶;
    mass(S) <=7M²*M*36M⁴+4M*225M⁶ =1152M⁷.

This is HAND source analysis, not a compiled coefficient-mass theorem. It bounds
every coefficient of S. A uniform row bound |f_m|<=T thus has the sufficient finite
test |lambda|*1152M⁷+|Delta|^5*T<p. A centered arbitrary a may have size p/2;
M cannot be declared small until the exceptional conic argument gives |a|<=3B².
[pcc:unverified]

## Restricted asymptotic consequence — hand transfer

For fixed support, B=p^o(1), L=H1³ H2²=p^(1-o(1)), H1,H2>=1 and weighted norm<p,
the source anchor bounds are

    |lambda|<=n0=floor((p-1)/(B⁵ L));
    |c|,|d|<=n1=floor((p-1)/(B⁴ L));
    |f_m|<=T=floor((p-1)/L).

All three are p^o(1); zero compatible-image size is permitted. On the exceptional
branch the centered conic first gives a=p^o(1) in magnitude, so M=p^o(1). The
cross bound becomes p^o(1)<p eventually. Also H1<=p^(1/3) from L<p, so the
exceptional linear bound is p^(1/3+o(1))<p;6B²<p eventually. Consequently, within
this declared family and regime, centered coefficient lifting adds no independent
remaining-coordinate equation on the exceptional branch. The asymptotic/support/
weighted-norm transfer remains HAND; the compiled theorem is finite and conditional.
[pcc:unverified]

This does not cover multiple generators, higher support/degree, different height
regimes, saturation, infinity, useful density of other branches, or all ECDLP.
No numerical/field/curve/LLL/native qualification/paid execution occurred. The
prepared independent Sage control remains unexecuted under the existing unknown
shared charged/reserved balance and missing runtime/caller/capacity/custody.
[pcc:unverified]

## Informed successor

Retain the two CURVE-DEPENDENT sources F1*W² and F2 separately. Their common
profile is(2,2), not the canceled primitive's(3,2). For
J=lambda*W²*F1+mu*F2 after both translations, proposed anchors are lambda at
x²y²V²W², mu at U²X²,2mu*tau at UVX², and2mu*sigma at U²XW. These would recover
both offsets jointly when2mu!=0 while retaining curve parameter b. The hypothesis
is an economical complete selector for this rank-two span, not a useful-yield
claim. Next source obligation is to verify these against the entire original J;
then account for mu=0 and all coefficient/row multiplicities before any algorithm
or rate claim. Neither empirical admission nor complete-algorithm status changes.
[pcc:unverified]
