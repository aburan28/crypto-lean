# Tree representations, root budgets and a joint-search successor

16 November 2026. This round checks a complete known-tuple representation
constructor and an exact root-shortlist budget, then identifies what must
change in a selector. The original goal is still a complete classical
subexponential prime-field ECDLP algorithm. No numerical experiment,
benchmark, native qualification or paid job was run. PCC is unverified.

## Exact root budget without a uniform-output assumption

Let A be a finite first-world information/coin space. Independently draw
raw right-color records x:(Fin s x Fin b)->G in a finite additive group G,
with s>0 and r=|G|. Let F:A->Finset G be ANY target-selection function with
|F(a)|<=L. Its internal selection may be coordinate-dependent and adaptive
within A. For each fixed a it cannot depend on the sampled right array.
The new shared endpoint is

    card{(a,x) | exists g in F(a), c:Fin s->Fin b,
                       tupleSum(c,x)=g} * r
      <= card(A) * L * b^s * r^(s*b).

After normalizing the actual raw product-space count, success is at most
min(1,L*b^s/r). Selected targets need not be uniform, pairwise independent,
or independent of their own first-world inputs. The original root zero-sum
test uses targets g=-U for shortlisted left subtotals U. This is an upper
bound for the permissive point-match event, so further coefficient/label
validity tests cannot enlarge it. [pcc:unverified]

The proof uses a more general finite family f:C->(H->+G) of surjective
additive homomorphisms. Existing equal-fiber and kernel-cardinality laws
give card{x | f(c)(x)=g}*r=|H|. The finite witness space

    Sigma a, Sigma g in F(a), Sigma c, {x | f(c)(x)=g}

projects surjectively onto successful (a,x) worlds. Existing surjection
cardinality and finite Sigma sums give |A|*L*|C|*|H|. Substitute the unchanged
PartiteCoverage.tupleSum_surjective, |C|=b^s and |H|=r^(s*b). No curve-specific
probability law or generic variance proof is re-derived. [pcc:unverified]

The final probe applies the endpoint unchanged to actual Mathlib
Weierstrass point subgroups over ZMod p, deriving finiteness and NeZero p
from existing structures. Three named laws live in Group.ShortlistCompletion.
The model keeps full raw array multiplicities. The target Finset is only
an upper-bound projection of records; it is not permission to erase full
primitive provenance in an algorithm. [pcc:unverified]

For balanced m approximately sqrt(n), n=ceil(log2 r), b=ceil(r^(1/m)), and
s approximately m/2, the hand consequence is

    success <= L*2^(-n/2+O(n/m+m)).

If L<=T and the original per-attempt target T is 2^(O(sqrt(n)*log n)) in
the standard input-bitlength regime, this is2^(-n/2+O(sqrt(n)*log n)), below
the proposed useful-yield floor2^(-O(sqrt(n)*log n)). Global clean rejection
is separate: divide a raw bound by Pr(clean) when that probability has been
established. A constant lower bound on it does not change this exponent.
This is a hand asymptotic application of the exact finite count.
[pcc:unverified]

### Precise architecture and exclusions

The scope is an EXPLICIT bounded target set formed without access to the
right input, followed by any completion search on the original right colors.
It even allows the right side to consider every original right tuple. Shared
auxiliary pools/coins independent of right inputs can be conditioned on or
included in A; count the union of all targets actually supplied by them.
Repeated representations of the same target do not create new independent
right-input opportunities. [pcc:unverified]

If right data chooses which left contexts will be generated, a single
side-local F no longer models the algorithm. A compact circuit representing
an exponentially large target set is not covered by a cap on its circuit
size. Joint/cross-half search, overlapping primitive supports, other output
contracts and implicit families need their own analyses. This is not a
general ECDLP, generic-group, coordinate-query or selector lower bound.
Fresh auxiliary records retained in a larger final relation require their
own output/yield/recovery contract; the application here keeps the original
one-per-color output and cancels compatible auxiliary records.

Controls: s=0 is excluded because its tuple sum is constant rather than
surjective. b=0 and L=0 are covered by the finite theorem as empty-event
cases. Taking F(a)=G makes the bound potentially vacuous, as expected.
No assumption about a uniform selected-output law was inserted.

## A complete representation constructor when the tuple is supplied

This is a hand control algorithm whose input ALREADY includes a selected
tuple X1,...,Xm with sum0. It does not find that tuple. Fix a binary tree
on the m leaves and a fixed symmetric subset S. For an internal node with
original child subtotals U,V and incoming offset a, try a local shift t and
send offsets a+t to the left child and -t to the right. The child outputs
are U+a+t and V-t, whose sum is U+V+a. Descendant choices do not change
this admitted parent output. [pcc:unverified]

Precompute original subtree subtotals in O(m) group additions. Start at
the root with a=0. Visit nodes top-down. At each node reveal only its own
independent uniform shift pool, choose the first tag for which both child
outputs lie in S, and fail if none passes. Continue with the resulting
child offsets. This is an executable finite prescription for the supplied
tuple, with no discrete-log labels read. [pcc:unverified]

Suppose q(W)=|S intersect(W-S)|/r>=q0>0 for EVERY W in G. Conditional on
all earlier revealed pools and the supplied tuple, the next pool is still
raw uniform and independent. Its failure probability is at most(1-q0)^k.
With J=m-1 internal nodes, sequential conditioning and a union bound give

    Pr[constructor fails] <= J*(1-q0)^k <= J*exp(-q0*k).

Choosing k>=q0^-1*ln(J/epsilon) gives success at least1-epsilon for m>=2.
The previous hand interval estimate supplies q0=1/(16b^2) under its explicit
p>3/large-subgroup conditions, giving k=O(b^2 log(m/epsilon)). Do not replace
that fixed gate/condition by every random marker threshold or by a
clean-conditioned pool law. These are hand probability/cost statements;
the new Lean module formalizes the separate root budget. [pcc:unverified]

Charge O(m*k) pool tests/group operations plus point generation, key
evaluations, coefficient records and final checks. Public scalar-multiple
sampling adds its O(m*k*log r) group-operation cost. Each local auxiliary
coefficient enters the two child subtrees with opposite signs. Induction
on subtree addition leaves exactly the original primitive coefficient
vector at the root; local planted-zero outputs are not substituted for it.
This coefficient/cost argument is hand scope here. [pcc:unverified]

The constructor reads BOTH child subtotals of the supplied tuple when it
chooses an ancestor tag. It therefore is not an independent-half shortlist
algorithm and does not contradict the root budget. Implementing it as a
search over all unknown tuples must charge ancestor-offset contexts, all
local tag choices, retained states and recovery. A small successful
certificate or a cheap constructor for a known witness is not an extractor.

## Concrete successor: overlapping original supports

One way to leave the independent-half model is to split coefficient vectors
over ALL original records, instead of assigning disjoint color halves.
Let w be the final one-per-color coefficient vector. Use u in {0,1}^B0 and
v in {-1,0,1}^B0 with u+v=w. Coordinatewise, allow

    w_i=0: (u_i,v_i)=(0,0) or (1,-1),
    w_i=1: (u_i,v_i)=(1,0) or (0,1).

These are the established overlapping-representation identities from the
primary subset-sum literature, not a novelty claim. Both candidate parts
can now use inputs from all colors, so the root theorem's independent
completion-space hypothesis does not hold. [pcc:unverified]

A sparse version fixes a selected coordinates with v_i=+1 and h-a unselected
coordinates with v_i=-1. For a final vector w of weight m, its exact hand
representation count is

    R = binom(m,a)*binom(B0-m,h-a),
    weight(v)=h, weight(u)=m+h-2a.

Candidate sizes, sparse provenance and legality testing must be priced.
Group-sum equality alone is insufficient: u+v must have exactly one unit
coordinate in each original color, no negative/2 entries, and nonzero full
primitive provenance. The original point-only/private-label recovery
obligations remain. [pcc:unverified]

Two genuinely joint mechanisms now warrant a discriminating test: the
implicit block/resultant interval-gcd query in the previous report, and
filtered generation of the overlapping sparse u,v families with exact
compatibility recovery. Neither currently has a capped construction/yield
bound. Integer modular dot-product filters are not supplied by an elliptic
point encoding; selecting an independent coefficient checksum with an
unknown target would add its own success loss. No integer subset-sum
exponent, compatibility-circuit speedup or generic group algorithm is
transferred to ECDLP here. [pcc:unverified]

## Evidence and prior review

Prospective plan8b8ea10 and inherited floor22614e8 precede source0ad8012.
Build002 and actual-field assembly001 pass. Floor001's unanchored zero
codomain and build001's unresolved natural self-casts remain with original
sources/logs. Existing laws fixed those implementation errors without a
new hypothesis, trust change, proof-limit increase or linter suppression.
Canonical gate001 audits215 theorems with0 failures and0 trusted-native
exceptions. All3 named axiom receipts use only standard allowed axioms.
No fresh checker or hosted pass is asserted. [pcc:unverified]

KB unavailable: no loaded knowledge/theorem connector and unusable inherited
wrapper. Bounded fallback used current C/arbitrary-target reports, the prior
fixed-anchor B calculation (the same union-bound principle), PartiteCoverage,
and exact Mathlib equal-fiber/kernel/projection/Sigma declarations. This
round extends the quantified selector scope rather than claiming a new
union-bound method or a general impossibility result.

Primary sources read:

- [HGJ2010 slides9--14](https://www.iacr.org/conferences/eurocrypt2010/talks/knapsacks.pdf): overlapping index representations and integer modular filters, with generation costs explicit.
- [Wagner2002 author version](https://people.eecs.berkeley.edu/~daw/papers/genbday.html), sections2--3: scalar/XOR/group-specific merging; no blind-signature scalar access transferred to DLP.
- [Randolph--Wegrzycki sections2.1--2.3 and3.1](https://arxiv.org/html/2511.10823): input integer dot products, modular filtering, mixing and compatibility requirements.
- [Li--Ye sections1.1--1.2](https://arxiv.org/html/2610.10446): overlapping coefficient representations, integer hash-filtered generation and compatibility testing. No runtime exponent imported.

The report's diagrams/PDF separate supplied-witness construction, the exact
side-local cap, and proposed joint alternatives. No empirical data exists
to plot; canonical measured graphs have no new value or completed-algorithm
edge to update. All older owner claim subjects and frozen consumer evidence
histories remain unchanged. PR20 landing/zero-step hosted billing failure
and queued scoped autonomy/outcome land with this substantive change.

| User requirement | Current evidence / remaining dependency |
|---|---|
| New selector ideas beyond the tensor route | Exact block query and overlapping sparse-support interfaces proposed |
| Audit full tree rather than one join | Known-tuple hand constructor and conditional union-bound budget |
| Avoid unproved selected-output uniformity | Exact side-local shortlist count, actual prime-field instance |
| Demonstrate complete end-to-end subexponential algorithm | Unmet: joint implicit construction, actual useful yield and complete recovery/cost missing |

The original cost/yield targets remain unchanged; this scoped architecture
test does not meet them. Frozen numerical qualification still needs its
checkpoint access, and no execution authorization was expanded.
