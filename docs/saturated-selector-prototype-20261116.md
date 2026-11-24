# Subcritical coordinate charts for a certifying selector

16 November2026. Source23640c9, unexecuted Sage candidate. The new opening is
**coordinate translation with a rational height slightly below sqrt(p)**.
It has a hand-proved coverage bound. Useful lattice equations and a complete
subexponential ECDLP algorithm remain unproved. No Sage, curve, LLL, numerical,
paid or qualification run occurred. [pcc:unverified]

The [prospective plan](saturated-selector-prototype-20261116-plan.md),
[source](../research/saturated_selector_prototype_20261116/README.md),
[editable flow](saturated-selector-prototype-20261116/flow.dot),
[PDF](saturated-selector-prototype-20261116/report.pdf) and
[publication boundary](saturated-selector-prototype-20261116/PUBLICATION.md)
retain the hypotheses, controls and scope. [pcc:unverified]

## Three constructions, with different outcomes

| Construction | What it changes | Current conclusion |
|---|---|---|
| Ordinary balanced homogenized S3 ideal | Mixed shifts in (p,F1,...,Fs)^t | Prior generic filtration excludes the usual HHG-short certificate at H>=sqrt(p). |
| Explicit local subresultants | Add two linear vertex equations and a resultant, with V,V²,V³ witnesses | Constant local degree does not evade the same obstruction at chain length>=4. Keep as a negative control. |
| Translated subcritical charts | Replace each internal coordinate by tau+U/V, with H below sqrt(p) | Cover every finite coordinate tuple at a quantifiable cost; short independent equations remain the test. |

The global modular saturation mode remains a separate, unexecuted alternative.
Its cost and useful output are unknown. A short row alone is insufficient.
The source uses bounded Macaulay shifts, not Ryan's optimal D-Groebner shift
selection. [pcc:unverified]

## Exact local identities and their failed shortcut

For adjacent quadratics in one internal projective slot write

    F=aU²+bUV+cV², G=dU²+eUV+fV²;
    L=ae-bd, M=af-cd, N=bf-ce, R=M²-LN.
    V(LU+MV) = aG-dF;
    V²(MU+NV) = (aU+bV)G-(dU+eV)F;
    V³R = [a(MV-LU)-LbV]G + [-d(MV-LU)+LeV]F.

The last identity has a prior compiled generic owner. The first two are hand
algebra here; all three are exact modular identity checks in the UNEXECUTED
source. Multiplying by D³/V^k, D=product(V_i), gives a common D³ witness.
There are at most4m-7 generators, with total degree at most16 for local
resultants of the original S3 rows, independent of chain length.
These facts do not imply shortness. [pcc:unverified]

At m>=4 each vertex has a neighboring projective slot. A boundary linear
subresultant has degree1 in its own slot plus2 in its neighbor; its resultant
has degree4 in the neighbor. Interior versions have still higher projective
degree. Every nonzero generator therefore has total projective degree>=2.
The prior filtration applies to their centered integer lifts and all ordinary
mixed shifts. At balanced H>=sqrt(p), no nonzero HHG-short row follows from
this local augmentation. At m=3 there is no neighboring slot: degree1/0
terms are an explicit exception. This rejected shortcut was caught before
execution. [pcc:unverified]

## Positive rational pairs give a coverage bound

Let p be prime, 1<=H, H²<p, and

    P_H={(u,v):1<=u,v<=H, gcd(u,v)=1};
    S_H={u/v mod p:(u,v) in P_H}.

Reduction is injective on P_H. Equality modulo p implies p divides
u*v'-u'*v. Its absolute value is at most H²-1<p, so it is zero as an integer.
Two positive primitive pairs representing the same rational number are equal.
Thus |S_H|=|P_H|. This is hand elementary number theory. [pcc:unverified]

Every nonprimitive pair has some common divisor d in[2,H]. A union bound gives

    H²-|P_H| <= sum_(d=2)^H floor(H/d)²
               <= H² * sum_(d=2)^H 1/d² <= 3H²/4.

For H>=2, bound the last sum by
1/4+sum_(d=3)^H 1/(d(d-1))=3/4-1/H. H=1 is immediate.
Consequently |S_H|>=H²/4. No distribution of elliptic-curve coordinates,
character sum or independence of selected decompositions is assumed.
[pcc:unverified]

For any FIXED finite coordinate x and uniform tau in Fp,
x-tau is uniform, so Pr[x-tau in S_H]=|S_H|/p>=H²/(4p).
Translate s=m-2 slots independently. For every fixed finite tuple,

    Pr[all slots have x_i=tau_i+u_i/v_i with 1<=u_i,v_i<=H]
      >= (H²/(4p))^s.

Take H=floor(sqrt(p)/2). For p>=16, H>=sqrt(p)/4, giving q>=64^(-s).
An iid pool of N offset vectors misses any of the p^s tuples with probability
at most p^s*(1-q)^N <= exp(s ln(p)-qN). Hence

    N >= ceil(64^s * (s ln(p)+ln(1/epsilon)))

suffices for simultaneous coverage with failure probability at most epsilon.
The simultaneous event permits adaptive tuple reuse. Pool construction does
not enumerate p^s tuples. The existing generic finite-pool reasoning can be
reused; this counting/application is hand analysis, not a new Lean theorem.
Infinity tuples are excluded and require separate charts or path treatment.
[pcc:unverified]

## How much shrink can be afforded?

For H approximately sqrt(p)/L, the sufficient chart-pool size is
(4L²)^s times a logarithmic universe factor, subject to integer rounding.
There is also a matching counting lower bound for a pool covering ALL p^s
finite tuples: each offset vector covers only |S_H|^s<=H^(2s) tuples.
Thus N*H^(2s)>=p^s. With L=sqrt(p)/H exactly,

    L^(2s) <= N <= ceil((4L²)^s*(s ln(p)+ln(1/epsilon)))

is a necessary lower bound and a probabilistic sufficient upper bound.
For fixed epsilon and L>=2, universal chart coverage is subexponential
precisely in the window s*ln(L)=o(ln(p)). The lower bound is about covering
all tuples by these boxes, not about every possible ECDLP selector.
[pcc:unverified]

If m=o(log p), constant L has exp(O(m)) overhead. For
m=Theta(sqrt(log p/loglog p)) and fixed A>0:

| Height | Sufficient coverage cost | Implication |
|---|---|---|
| sqrt(p)/2 | exp(O(m)) times poly(log p,m) | Subexponential chart overhead. |
| sqrt(p)/(log p)^A | exp(O(m loglog p)) | Still subexponential. |
| sqrt(p)/B^kappa, fixed kappa>0 | At least B^(2kappa*(m-2)) | Universal coverage costs p^(2kappa+o(1)) if m grows and B^m is approximately p; outside the goal. |

The last row is a cost of THIS universal covering strategy, not a lower bound on every
possible chart method or a promise restricted to realizable tuples. A future solver must demonstrate useful equations
within an affordable shrink window or prove a different coverage method.
Lower height removes the prior theorem's hypothesis; it does not prove that
LLL finds even one useful independent equation. Coefficient height, determinant,
root degree and original decomposition yield still govern the full task.
[pcc:unverified]

## Executable source contracts, without execution evidence

The worker validates the public prime-field/subgroup input, fixes an interval
catalog, forms mixed targets alpha*G+beta*Q, and passes only each point to the
selector. Original catalog indices, repeated occurrences and signs are
retained. For each capped external chart vector it substitutes
(U_i+tau_i V_i,V_i) into the original homogeneous S3 path. This is a coordinate
change; it does not translate points in the group. Every attempt and offset
is recorded and charged globally. [pcc:unverified]

The three source modes are ordinary, local_minors and full modular saturation.
Exact D^n*g=sum(A_i F_i) witnesses are verified before modular constraints
are lifted to integers. Full finite shift-family counts precede construction.
Rows are grouped by projective multidegree; exact LLL transformations, scale
divisibility and the integer L1 bound below p^t are checked. Homogeneous
integer identities are dehomogenized only afterwards. [pcc:unverified]

The lexicographic projection checks Groebner membership in both directions
and Buchberger critical pairs. A capped exact standard-monomial staircase
admits finite leaf recovery; no potentially overflowing CAS dimension scalar
is trusted. Rational candidate leaves are filtered through the fixed catalog,
then original signs and actual point sums are checked. Extra projected roots
are allowed; no bounded-ratio or completeness claim is made. [pcc:unverified]

Incremental factor-base elimination retains original target provenance. A
nonzero dependence cancels the catalog; recover -A/B only for B!=0 and check
that scalar times G equals Q. A separate point/scalar replay repeats the
relations without saturation, LLL or root finding. It is producer-written
source, not an independent signed verifier. Standard free-label probability
is conditional on truly uniform labels and a label-free selector; it is not
asserted for wall-time-censored or fixed toy controls. [pcc:unverified]

The launcher applies direct process-group deadlines, CPU/address-space and
per-log output limits to workers and replay, with cleanup on every exit path.
Aggregate memory requires the future container limit. One global budget spans
all chart/length/profile/target attempts, including failures. Caps and timeouts
never certify emptiness. All scientific stages remain UNEXECUTED.
[pcc:unverified]

## What was checked and what remains

Source23640c9 parses seven Python and seven JSON files. Nine generic
resource/count/fake-client development controls pass, including missing
runtime, preserving existing evidence and group timeout. Launcher help exits0.
No Sage arithmetic is imported by those controls. Prior canonical Lean271/0/0
covers earlier mathematical modules; no Lean file changed here and that gate
does not verify this Python/Sage candidate. [pcc:unverified]

The paired public toy protocol retains its original ordinary/global-saturation
inputs and zero-short-row ordinary prediction at balanced height. A DISTINCT
subcritical fixture/protocol uses H=2 for the same published toy; its arbitrary
fixed offset panel is not an iid covering pool, and the balanced zero-row
prediction does not apply. No fixture has been run. Identity/catalog/two-sum
success cannot substitute for lattice-path usage. [pcc:unverified]

Both packets have proposed USD2 all-in ceilings, concurrency1 and zero retries;
these are not grants, spend estimates or launch requests. The Sage10.8 base
manifest is digest-pinned through read-only registry metadata, not pulled,
built or qualified. Source-image custody, actual caller/pool permissions,
live capacity and known daily/monthly unreserved balance remain prerequisites.
The requested existing cost/reservation record is still missing. No backend
substitution, numerical run or paid build was made. [pcc:unverified]

Next discriminating obligation: show a charged lattice determinant/short-row
argument in the constant/polylogarithmic shrink window, then independent
finite-root extraction and useful random-target relation yield. An admitted
small control can falsify mechanics; it cannot establish asymptotics. The
original complete end-to-end algorithm criterion remains unmet.
[pcc:unverified]

## Source provenance

The primary-source index records Ryan2025 chapter3; pinned cuso API/default-L1
context (no code copied); Sage official interface documentation; CHHS2016
univariate/binomial scope and CHHS2021 independence scope. None is cited as a
generic nonlinear solver theorem. The public toy is David Ahlqvist2022,
U.U.D.M.2022:49, pp15--16/table1, reproducing Paar--Pelzl Example9.5. KB tools
were unavailable; bounded primary/owner/Mathlib fallback and a targeted web
search support no novelty/absence claim. [pcc:unverified]
