#set page(paper:"a4",margin:16mm)
#set text(font:"DejaVu Sans",size:9.7pt)
#set par(leading:0.4em)
#text(size:19pt,weight:"bold")[Concentrate the height budget; match the rows]
#v(4pt)
16 November2026 · source1a140f8 · PCC unverified

The new candidate spends most rational-height shrink on one/few internal
coordinates, with a sparse modulus-monomial menu. It passes a necessary
leaf-support test at subexponential chart cost. It does not yet establish
useful short equations, finite root cost or a complete ECDLP algorithm.

#image("flow.svg",width:100%,height:145mm,fit:"contain")

*Executed source checks.* Fifteen generic laws and eight actual semantic
checks compile. Full canonical all-tracked audit exits0:293 theorems,
zero failures, zero trusted-native proofs. Every actual named axiom print
uses standard axioms only. No Sage, curve/LLL numerical, paid or qualification
run. Existing137 pinned subjects and twelve-row history remain intact.

*What changed the direction?* Uniform fixed-multiplicity shrink can be too
expensive before a leaf-dependent certificate is even eligible. Low-row-rank
blocks alone also miss a modulus-support gap. Unequal heights plus matched
sparse rows form a different, still untested successor family.

#pagebreak()
#text(size:16pt,weight:"bold")[An exact support threshold and its escape window]

The existing filtration says that a nonzero coefficient c of projective
degree d in the ordinary ideal power is divisible by p^(t−floor(d/2)), with
natural subtraction. For integer H≥1, H²≤p, the new compiled bound is
#raw("H^(2t) ≤ |c| H^d.",block:true)
Let e=max(t−floor(d/2),0). Divisibility gives |c|≥p^e≥H^(2e), and2e+d≥2t.
If the monomial has positive leaf degree, its coefficient weight is at
least B H^(2t). Since L1 is at least any one term, the compiled consequence is
#raw("L1 < p^t and B H_min^(2t) ≥ p^t
  => every positive-leaf-degree coefficient is zero.",block:true)
A generic weight lower bound and a finite product-height law admit unequal
per-slot heights. Actual translated four-leaf S3 generators, ordinary ideal
powers and two-slot weights are checked. This is not a saturation theorem.

Write H_i=sqrt(p)/L_i, L_i≥2, s=m−2. Positive primitive pairs give at least
H_i²/4 distinct residues per slot. Signed fractions occupy at most3H_i²
residues after normalizing denominator positive. Hand counting gives
#raw("Necessary universal signed-box pool:
  N ≥ product_i(L_i²/3).
Sufficient iid pool, failure at most epsilon:
  N ≥ ceil(product_i(4L_i²) [s ln p+ln(1/epsilon)]).",block:true)
Thus affordable universal coverage is exactly sum log(L_i)=o(log p), for
fixed error. These are hand applications; infinity/promise sets are separate.

*Uniform cost.* Uniform L must satisfy L^(2t)>B before a leaf term is
possible. If t is fixed, m grows, m=o(log p), and B^m≈p logarithmically,
universal coverage costs at least p^(1/t−o(1)).

*Concentrated candidate.* One L_i=B^kappa with kappa>1/(2t), all others2,
escapes that support exclusion. Its sufficient coverage cost is
B^(2kappa) exp(O(m)) times a logarithmic factor: subexponential when
log B=o(log p), m=o(log p). No equation existence is implied.

*Fair control.* Fix the same total dyadic shrink K. Uniform k_i≈K/s may be
excluded while concentrated k_i remain eligible. The worst-case chart
budget is the same. This is an eligibility separation, not a measured win.

#pagebreak()
#text(size:16pt,weight:"bold")[Row count helps; modulus separation limits it]

For ordinary chain powers e_0,...,e_(m−2), the projective grade at slot j is
2(e_j+e_(j+1)). The head e_0 and adjacent sums determine every exponent.
A fixed profile with total power at most t therefore has at most t+1 records.
With a finite shift menu M, one shifted profile has at most(t+1)|M| records.
These injection/cardinality laws are compiled; actual chain indexing is
checked. Original index multiplicities are retained even for equal polynomials.

This bounds row rank per block, not columns, determinant, short-vector
quality, all-block cost or independent equations. Classical LLL loses an
exponential factor in rank. That factor and L1 conversion must be compared
to an actual determinant/minima margin, which is unknown here. Ryan2025
printed pp5–6 and chapter3 are the primary context; fixed-ideal optimality
does not establish nonlinear independence.

There is a second compiled test. Let I be the chosen integer-lift ideal,
whose generators have projective weight at least2. Degree0/1 pure modulus
shifts occupy only weights0/1. A combination has the form
#raw("f=a+p^t b,  a in I,  b supported in weights0/1.
At coordinate scales≥1, L1(f)<p^t forces b=0.
Therefore f remains in I.",block:true)
Any nonzero low coefficient would have magnitude at least p^t. The generic
modulus-part lemma and its original-ideal consequence compile; an actual
translated S3 application checks the support interface.

This is NOT an unconditional extraction impossibility. A proper lift ideal
with nonempty positive-dimensional leaf projection would prevent a finite
nonempty projection from its short subideal. That extra premise is not
proved for arbitrary independently centered lifts. They cannot silently be
identified with the exact characteristic-zero S3 curve ideal. Other lifts,
saturation and higher matched modulus rows are outside this test.

*Concrete new menu.* Include1 and every monomial in each ordinary S3 row's
support. Its size is O(m), degree at most6; it puts p^t rows on the original
coefficient columns. At fixed t, full power records are bounded by
choose(m−1+t,t)|M|; one block by(t+1)|M|. The dense column upper bound is
choose(3m−4+6t+6,6t+6). Actual rank/bit heights and every failed block still
count. This is a proposed sparse family, not an optimal-shift implementation.

#pagebreak()
#text(size:16pt,weight:"bold")[Freeze profiles, then test the missing gain]

A dyadic grid chooses k_i≥1, sum k_i≤K, H_i=floor(sqrt(p)/2^k_i)≥1.
There are at most choose(K,s) profiles, each retaining any finite tuple
with probability at least2^(−2K−4s). One shared iid offset pool of size
#raw("ceil(2^(2K+4s) [s ln p + ln choose(K,s) + ln(1/epsilon)])",block:true)
covers all tuple/profile pairs simultaneously with failure at most epsilon.
Both profile enumeration and this pool are subexponential for K=o(log p),
since s≤K and choose(K,s)≤2^K. This is HAND counting/probability; it does
not bound the solver work per profile. Adaptive choices use the fixed
simultaneous event, not selected-output uniformity.

*Next discriminating comparison.* Keep catalog, target, labels, multiplicity,
matched menu, total shrink and counted resources fixed. Compare uniform
against concentrated heights. Record exact short rows, leaf support, finite
leaf projection, original signs/point decomposition and scalar replay as
separate outcomes. Preserve all caps/empty/error profiles. Existing pinned
prototype has scalar height and degree0/1 shifts; it is unchanged and does
not implement this successor. No scientific trial was run here.

*Formal boundary.* Twelve HeightBudget and three ChainPowerBlocks laws;
eight semantic declarations; canonical293/0/0 exit0 and fifteen actual named
axiom prints. The coefficient threshold, finite product/count and support-gap
statements are formal. Signed/anisotropic/dyadic pool asymptotics, S3 family
cost interpretation and candidate menu are hand analysis. No new custom
axiom, sorry, native_decide, trust/limit/inventory/linter exception. Initial
compiler/time-limit failures and focused fixes are retained; no limit raised.

*Still required.* A positive determinant/minima margin beating LLL loss;
independent useful equations across the whole chain; charged finite-root
recovery; useful original random-target yield; and complete cold scalar
recovery cost. A toy can falsify mechanics, not establish asymptotics.
The complete classical subexponential prime-field ECDLP criterion is unmet.

*Execution boundary.* No Sage/curve/LLL numerical/native, paid or qualification
run. The existing live cost/reservation record remains missing; source-image,
caller/capacity/custody and budget admission remain necessary. Earlier hosted
CI failures were explicit zero-step billing lock, not passes or a reason to
retry/pay. Source continuation is separate from PR monitoring authority.

*Evidence.* Existing owners BalancedFiltration, UniversalPools, Semaev.S3;
pinned Mathlib cfc55fc58714a59dc06e6e79edc6d1d95140d3c2; Ryan2025 thesis
hash7e0bde57bdcaa791c801240ea7c30be7263861ad2329cf998f1c5628bad0eec3,
printed pp5–6 and55–68. KB unavailable, bounded primary/owner/Mathlib fallback;
no novelty or absence claim. Attestation remains unverified.
