# Curve-first pruning and triangular mixed-degree selection

16 November2026. New HAND derivations, plus seven separately compiled generic
degree-one identities and four symbolic application/recovery declarations.
No selector execution. The earlier [component](first-order-selector-20261116.md)
contains the compiled rank-one model; its347/0/0 audit does not certify the
general mixed-degree argument or new norm/model-count bounds below. No numerical, curve/LLL, paid or qualification run.
The complete classical subexponential prime-field ECDLP goal is unmet.
[pcc:unverified]

## 1. Reject multipliers before enumerating offsets

Keep exactly the first-endpoint model and weights of the published component.
Let p>=5 be prime, B>=2,H>=1 integers, and let [z] denote the unique centered
integer representative modulo p. Put lambda in the signed first window and
c=[2lambda*tau] in the second window:

    0<|lambda| <= floor((p-1)/(B^4 H²)),
    |c| <= floor((p-1)/(B² H²)).

Every norm-short row in the declared family supplies such a pair through its
no-worse centered representative. The complete20-column table partitions into
nine offset-independent columns, five linear-offset columns, three quadratic
columns and three remaining columns. The static AST receipt checks that this
is an exact partition, without running source arithmetic. [pcc:unverified]

Write A=[-2a*lambda], T=[lambda*tau²]. The nine constant columns contribute
exactly

    H² ((B^4+2B²)|lambda| + (B²+2B³)|[-2lambda]|
        + 2B|A| + |[-4b*lambda]|).

There is no wrap in [-2lambda]: |lambda|<p/16 follows from B>=2. Nor does
[-2c] wrap, since |c|<p/4. The five linear columns therefore contribute
exactly H²(4B²+2B³)|c|. The three quadratic columns contribute

    B² H² (2|T| + |[-2T+A]|) >= B² H² |A|.

The last inequality is the triangle inequality for centered residue distance:
2T+[-2T+A] represents A, whose centered representative minimizes absolute
value. The remaining three columns have nonnegative norm. These are disjoint
groups; no coefficient is counted twice. Combining gives the necessary bound
[pcc:unverified]

    L1 >= C(lambda) + D |c|,
    C(lambda)=H² (B²(B+2)²|lambda|
                       + B(B+2)|[2a*lambda]| + |[4b*lambda]|),
    D=2B²(B+2)H².

This handles negative lambda, zero a or b, c=0 and any tau. Thus a faster
exact enumeration can use

    0<|lambda| <= floor((p-1)/(B²(B+2)²H²));
    skip lambda if C(lambda)>=p;
    otherwise |c| <= floor((p-1-C(lambda))/D).

Derive tau=c/(2lambda), then use the unchanged complete-row norm/witness test.
These are necessary tests, so the pruning preserves the original existence
search. This is a proposed successor, not a change to the frozen Python source.
An implementation must retain a bound witness and the exact multiplicity of
every pruned integer interval; caps still mean incomplete. [pcc:unverified]

## 2. A viability warning for random curve models

Let n0,nA,nB be the integer cutoffs with respective weights
B²(B+2)²H², B(B+2)H² and H². For every admitted nonzero lambda, the maps
a -> [2lambda*a] and b -> [4lambda*b] are bijections on residues. Consequently,
the number of parameter pairs (a,b) for which ANY offset can pass the necessary
test is at most

    S = 2n0 (2nA+1)(2nB+1).

This deliberately forgets the sum in C and overcounts, so it remains an upper
bound. There are p²-p nonsingular short-Weierstrass models in characteristic
above3. The probability for a uniformly sampled nonsingular parameter pair
is therefore at most min(1,S/(p²-p)). For H=sqrt(p)/B^kappa, fixed kappa>2
and B=p^o(1), all three cutoffs are p^o(1), giving p^(-2+o(1)).
[pcc:unverified]

Allowing all p-1 nonzero short-Weierstrass scalings (a,b)->(a/u^4,b/u^6)
gives the union bound min(1,S/p), still p^(-1+o(1)). Each fixed scaling is a
bijection on nonsingular models. This does not cover arbitrary generalized
Weierstrass presentations or new factor bases with different bounds.
[pcc:unverified]

These are counts over RANDOM MODELS, not an estimate for a given curve and
not an ECDLP lower bound. For fixed a and uniform b, the weaker upper bound
2n0(2nB+1)/p is available. Small/special curve models may pass. The conclusion
is practical: a fast exact selector can still be almost always empty in its
declared model distribution. Do not mistake component completeness for yield.
[pcc:unverified]

## 3. Homogeneous multipliers do not remove that restriction

Try the larger block generated modulo p by x^i*y^(d-i)*F_tau, i=0..d, plus
p times EVERY support column. For a homogeneous multiplier M of degree d,
the top V² leaf coefficients reveal every multiplier coordinate. Shortness
bounds them by n=floor((p-1)/(B^(d+4)H²)). A nonzero short row has a nonzero
multiplier vector modulo p. [pcc:unverified]

The UV leaf-degree d coefficients are exactly -4b*M; the UV leaf-degree d+1
coefficients are exactly -2a*M*(x+y). For each fixed nonzero M, choose a
nonzero coordinate of M and of M*(x+y). These choices depend only on M;
the polynomial ring is a domain. They give invertible scalar maps in b and a.
The same count bounds the number of admissible curve models by

    ((2n+1)^(d+1)-1) (2n_a+1)(2n_b+1),
    n_a=floor((p-1)/(B^(d+1)H²)),
    n_b=floor((p-1)/(B^d H²)).

When the whole right-hand numerator is p^o(1), the random-model fraction
remains p^(-2+o(1)). Homogeneous rank growth alone does not defeat this test.
This does not refute mixed degrees, multiple generators or saturation.
[pcc:unverified]

## 4. New candidate: triangular pivots with mixed leaf degrees

Use ALL rows x^i*y^j*F_tau with i+j<=d, together with full p support rows.
There are r=(d+1)(d+2)/2 non-modulus rows. The following is a complete HAND
existence-search argument for this declared block. It needs a new source/model
implementation and independent checks before being treated as a tested selector.
[pcc:unverified]

The V² coefficient of F_tau is

    P_tau=x²y² -2tau*xy*(x+y)
           +tau²*(x-y)² -2a*xy -(2a*tau+4b)*(x+y)
           +a²-4b*tau.

Its unique leaf-degree4 term is x²y² with coefficient1. All other terms have
smaller leaf degree. For a proposed short row, enumerate its small coefficients
v_ij at the distinct pivot monomials x^(i+2)y^(j+2)V², i+j<=d. The cutoff is

    |v_ij| <= n_(i+j),
    n_s=floor((p-1)/(B^(s+4)H²)).

Process total degree downward. The coefficient at each pivot is the multiplier
coordinate mu_ij plus contributions from already determined HIGHER degrees.
Thus v uniquely reconstructs a multiplier polynomial M_v(tau,x,y), with
coefficients polynomial in tau. The zero pivot vector reconstructs zero and
cannot represent a nonzero short p-only row. [pcc:unverified]

Offset recovery uses only the two top layers. Let h be the highest degree with
a nonzero pivot, choose the largest i with alpha=v_(i,h-i)!=0 modulo p, and
read all missing/out-of-range pivots as zero. The homogeneous degree h part
of M has exactly those constant pivots. Its degree h-1 coefficient at index k is

    mu_(k,h-1-k)=v_(k,h-1-k)+2tau*(v_(k,h-k)+v_(k+1,h-k-1)).

Take the coefficient at x^(i+2)y^(h-i)UV in M*F. The UV coefficient of F is
2tau*(x-y)²-2xy*(x+y)-2a*(x+y)-4b. Lower multiplier layers cannot contribute
at leaf degree h+2. Since all top pivots beyond i vanish, the chosen coefficient is

    if i=h:  2alpha*tau;
    if i<h: -2alpha*tau-2(v_(i,h-1-i)+v_(i+1,h-2-i)).

Both have nonzero slope in odd characteristic. Enumerate a short integer value c
for this coefficient, with |c|<=floor((p-1)/(B^(h+2)H²)), and solve the ONE
linear equation for tau. Then evaluate the triangular reconstruction, multiply
by the actual F_tau, center ALL coefficients and apply the exact full norm test.
Retain every pivot/anchor/offset record and an integer row-combination witness.
There is no loop over all p offsets and no general root finder is needed here.
[pcc:unverified]

Completeness: any existing short row supplies its pivot vector and chosen anchor
value within these windows. Triangular uniqueness recovers its multiplier at the
true offset, and the nonzero linear slope recovers that offset. Centering gives
a no-worse representative. A nonzero pivot remains nonzero because its window
is strictly inside half a modulus. Conversely every accepted centered row lies
in the declared modular span by its explicit witness. As before, this searches
existence and minimal representatives, not every integer lift. [pcc:unverified]

The number of raw candidate records is bounded by

    (product_(s=0..d) (2n_s+1)^(s+1) -1)
        * (2floor((p-1)/(B²H²))+1).

There are at most20r support columns. For fixed d,kappa>(d+4)/2 and
H approximately sqrt(p)/B^kappa, the bound is O(B^E), where

    E=(2kappa-4)r-d(d+1)(d+2)/3+2kappa-2.

For B=p^o(1) this is a subexponential COMPONENT enumeration bound, times
polynomial arithmetic in d and log p. If d grows and kappa=O(d), charge
O(d³ log B) in the exponent, all support/record costs and the entire search.
None of this supplies a useful-yield lower bound or a complete ECDLP cost bound.
[pcc:unverified]

## 5. What this attempt changed, and the next discriminator

The one-row branch gained an exact hand pruning formula and a scoped random-model
warning. Homogeneous multiplier growth retains a parameter restriction. Mixed
degrees give a concrete higher-rank search with triangular pivots and linear
offset recovery; this replaces the preliminary general univariate-root idea.
Its curve-model intersection and useful equation independence remain unknown.
[pcc:unverified]

The smallest degree<=1 check has now passed: seven generic laws in
CryptoLean.Polynomial.MixedDegreePivots and four actual declarations compile.
They link V² to the actual endpoint, split its U/V coefficients, recover all three
pivots and compile each x/y/constant linear-recovery branch over a field with
2!=0. All seven actual named axiom prints use only standard axioms. This does
not formalize the all-degree search, the pruning norm or the curve-model count.

Next smallest authorized proof obligation: test the first interior degree-two
branch M_top=alpha*x*y, then formalize the finite triangular reconstruction and
centered existence-search equivalence for arbitrary fixed d. Preserve all raw
failures, and only afterward consider an admitted implementation trial.
The existing rank-one frozen source is not silently extended. No numerical trial
can be called successful or empty without actually running under admission.
[pcc:unverified]

Primary context: the actual S3 expansion and maintained polynomial/domain owners.
The preliminary fallback of univariate root finding was checked against Shoup,
*A Computational Introduction to Number Theory and Algebra*, beta1, chapter20.2,
Theorem20.13, printed306, author-hosted [PDF](https://shoup.net/ntb/ntb-b1.pdf).
It supports expected polynomial-time finite-field factoring, not a deterministic
ECDLP bound; the specific S3 linear anchor above needs no factoring subroutine.
The attempted AMS original-paper fetch returned403. No novelty claim.
[pcc:unverified]
