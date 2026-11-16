# Selector-tree assessment: prospective proof plan

16 November 2026. Before the first Lean edit of this family. Continue the
complete classical subexponential prime-field ECDLP objective; previous
formal/analytic components do not satisfy that criterion. No numerical,
native benchmark/qualification or paid execution is authorized/planned.
All5 older owner claims and consumer frozen histories remain unchanged.

## Discriminating questions

1. For a KNOWN original tuple, can independent node-shift pools preserve
   the ancestor subtotal while admitting both children? Check the exact
   offset recurrence and conditional union-bound inputs using the prior
   arbitrary-subtotal q(W) bound. This is a witness-representation control,
   not a selector for an unknown tuple.
2. Can a root shortlist depending only on one color half and independent
   public coins meet useful yield, even if its selection is arbitrary and
   coordinate-dependent? Test a finite count bound without assuming its
   selected outputs are uniform. This is the next formal target.

Let A be the entire left-information/coin space, independent of right raw
entries x:(Fin s x Fin b)->G. For arbitrary F:A->Finset G with |F(a)|<=L,
consider the event that some g in F(a) is the sum of one point from each
right color. The exact target is

    card{(a,x) | exists g in F(a), c, tupleSum(c,x)=g} * r
      <= card(A) * L * b^s * r^(s*b),

where r=|G|, s>0. G is an actual finite additive group. F can return targets
rather than left sums, absorbing the negation needed for a root zero-sum.
It need not be uniform, independent of its own inputs, or a random subset.
The independence constraint is its lack of access to right inputs.

After normalization, raw success <= L*b^s/r. At s about m/2, balanced
b=ceil(r^(1/m)), m about sqrt(log2 r), subexponential L gives an upper
bound2^(-n/2+o(n)), below the original useful-yield target. This is a hand
asymptotic consequence for this explicitly one-sided root architecture,
not an ECDLP or general selector lower bound. Globally conditioned-clean
inputs need their separate division/conditioning argument.

Shared auxiliary pools independent of both color halves can be put inside
A. A transformed target depending on their values still falls under F.
Count all distinct candidate targets submitted; repeated representations
cannot be counted as fresh independent opportunities. Cross-half adaptive
search, both-input-dependent state construction, overlapping primitive
supports and implicit unexpanded families are outside this bound.

## Six-field instance gate

1. Structure above: finite types, dependent sums/subtypes, Fintype cardinality,
   additive homomorphisms, and the already defined PartiteCoverage.tupleSum.
2. Existing laws as stated: AddMonoidHom.card_fiber_eq_of_mem_range,
   AddSubgroup.card_ker_mul_card_of_surjective, Fintype.card_le_of_surjective,
   Fintype.card_sigma, Finset.sum_mul/sum bounds, Nat.card identities;
   tupleSum_surjective and the actual right-array type are inherited.
3. Objects: first build a generic bound for an arbitrary finite family of
   surjective additive homomorphisms f:C->(H->+G), arbitrary F:A->Finset G,
   with H the independent right-world group. Success is a predicate on
   the actual product A x H. No proxy syntax or assumed sampler equation.
   Then substitute H=((Fin s x Fin b)->G), C=(Fin s->Fin b), f=tupleSum.
4. Assembly floor: type-check uniform-fiber and kernel-cardinality laws,
   finite dependent-sum/projection cardinality, and tupleSum surjectivity.
   Repeat at actual ZMod p Weierstrass subgroups, deriving NeZero p and
   finiteness through nonsingularPointEquiv. No extra mathematical hypotheses.
5. Missing only: target-fiber scaling interface from the existing equal-fiber
   theorem; generic adaptive-shortlist cover endpoint; its partite instance.
   The union bound is applied by a witness Sigma projecting surjectively
   onto successful worlds; do not re-derive a curve-specific probability law.
6. Inheritance table:

| Operation | Existing law | New glue |
|---|---|---|
| Right target fibers | card_fiber_eq_of_mem_range | compare with zero kernel |
| Fiber scale | card_ker_mul_card_of_surjective | inherited count |
| Successful worlds covered by witnesses | card_le_of_surjective | actual projection |
| Count witnesses | card_sigma, finite sums | endpoint arithmetic |
| Original right sums | tupleSum_surjective | substitute unchanged |
| Actual curve group | nonsingularPointEquiv / Finite.of_equiv | local instances |

## Proof chain before code

For one surjective f, every target fiber has the kernel's cardinality;
existing kernel-cardinality times r equals card H. For each (a,g,c), use
that equality on {x | f(c)(x)=g}. The finite witness type is
Sigma a, Sigma g in F(a), Sigma c, {x | f(c)(x)=g}.
Projection forgets witnesses and covers each successful (a,x). Apply the
existing surjection-cardinality bound, multiply by r, and distribute finite
sums. Each fiber contributes card H, giving |F(a)|*|C|*|H|. Apply the cap L
and sum over a. Substitute the existing tupleSum surjectivity, card_fun,
card_prod and card_fin for the partite endpoint.

Commit floor source/log before shared laws. No existing frozen source,
proof limits, trust or linter policy edits. One Lake process at a time;
preserve every failed source/log with fresh paths. Final actual-instance
probe, all-source gate and named axiom prints remain required. Preserve
unrelated ProjectiveVeluInstanceProbe.lean untracked.

## Tree control, hand scope before any formalization

For fixed original tuple, attach an incoming offset a to a node whose two
original subtotals are U,V. Given local t, send offsets a+t to the left
and -t to the right. Their outputs are U+a+t and V-t; their sum remains
U+V+a. Thus choosing descendants does not change an admitted ancestor
output. A node pool independent of previously revealed ancestor pools has
failure at most(1-q0)^k when q(W)>=q0 for every subtotal. A deterministic
first-passing-tag policy reveals only the current/ancestor pools; with J
internal nodes, a sequential conditional union bound gives failure at most
J*(1-q0)^k. This relies on a globally shared FIXED S and uniform q bound,
not every random marker realization or a clean-conditioned pool law.

The policy reads the known tuple subtotals. It neither finds that tuple nor
bounds dynamic-programming list sizes. Ancestor-offset contexts, local tag
compatibility and full primitive coefficients must still be charged. The
root-shortlist bound tests a tempting independent-half compression of that
constructor; it does not disprove all overlapping/adaptive constructions.

## Prior review before choosing this proof

KB unavailable: no loaded knowledge/theorem connector, inherited wrapper
unusable. Read current C/rank/arbitrary-target reports and source modules,
PartiteCoverage, prior fixed-anchor B assessment and old interval analysis.
The root count is the same union-bound principle used in the earlier
fixed-anchor schedule, now quantified over any side-local selector.
No novelty claim.

Read primary HGJ2010 slides9--14 and Wagner author paper sections2--3;
integer modular filtering and the required list-generation operation are
not automatically available on elliptic coordinates. Read Randolph/
Wegrzycki https://arxiv.org/html/2511.10823 sections2.1--2.3 and3.1, and
Li/Ye https://arxiv.org/html/2610.10446 sections1.1--1.2: their dot-product
mod-prime filtering uses supplied integer inputs, and representations can
overlap primitive indices. Borrow no complexity exponent or generic group
algorithm. Those overlapping supports and future-aware methods are outside
the prospective independent-half theorem and are possible successors.
