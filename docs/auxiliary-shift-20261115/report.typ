#set page(paper:"a4",margin:17mm)
#set text(font:"DejaVu Sans",size:10pt)
#set par(leading:0.5em)
#text(size:18pt,weight:"bold")[Auxiliary shifts with a marker-rank filter]
#v(5pt)
15–16 November 2026 · candidate C · shared source a078981

A finite marker threshold gives a compatible-representation survival bound
including ties. The actual fixed-filter count has exact first and second
moments. These are local source components; PCC standing is unverified.
No numerical or timing experiment was run.

#image("flow.svg",width:92%,height:108mm,fit:"contain")

*Concrete rule.* Fix U+V=0 in a finite additive commutative group G of order r.
Choose an ordered key with kappa(−P)=kappa(P). Draw b>0 independent uniform
markers M and an independent b-point shift pool T. Set tau to the smallest
marker key. Accept j if BOTH U+Tj and V−Tj have keys at most tau.
#raw("r^(2b) <= 2 * card{raw pools | some compatible tag passes both}",block:true)
The hand uniform-probability reading is survival at least1/2 for the fixed
valid original relation. No uniform key-image or distinct-key hypothesis.

*Finite proof.* The analysis bijection (M,T) -> (U+T,−U+M) reverses the two
minimum comparisons. Totality covers every raw pool by success or its swap
preimage. The events have equal cardinality, giving the bound by card_union_le.
Ties are retained. Swap is not an input sampler or a planted closing witness.

#pagebreak()
#text(size:16pt,weight:"bold")[Full provenance and exact raw-pool moments]

*Primitive coefficients.* On the actual Finsupp space over original and
auxiliary records, use leftj=e0+e1+fj and rightl=e2+e3−fl. The source proves
#raw("leftj+rightl-W = fj-fl\nleftj+rightl = W iff j=l\nW and leftj+rightl are nonzero",block:true)
where W=e0+e1+e2+e3. Same tags cancel auxiliary provenance and retain the
original colored relation. Cross-tag actual zero relations may instead have
a different, larger DLP output contract; they are not formal-zero identities.
A planted local T−T with full coefficient vector zero is inadmissible.

*Actual count, fixed filter.* For fixed S=−S and U+V=0, let Y be the number
of tags j for which BOTH U+Tj and V−Tj are in S. With delta=|S|/r, under the
raw Measure.pi of uniformOn univ, the shared source proves
#raw("E Y = k*delta\nVar Y = k*delta*(1-delta)\nE Y^2 = k*delta + k*(k-1)*delta^2",block:true)
The subtraction k−1 is real-valued. The two gates agree, so their
probabilities are not multiplied. Existing integral_fintype, translation
sum equivalence, integral_comp_eval, variance_sum_pi and variance_eq_sub
are applied as stated. No generic variance law is re-derived for a curve.

*Actual prime fields.* Both final probes use Mathlib’s nonsingular Weierstrass
point group and its subgroups over ZMod p, with p prime. Existing
nonsingularPointEquiv supplies finiteness. The normalized infinity-aware key is
#raw("kappa_p(P) = p*(P.xRep 1).val + (P.xRep 0).val",block:true)
and Point.xRep_neg supplies symmetry. The unchanged shared count endpoint and
all three moment endpoints type-check at these objects. No proxy model.

*Hand selectivity bound, separately scoped.* If all key fibers have size at
most2, exchangeability and collision-pair counting yield
#raw("1/(b+1) <= E_marker[filter density] <= 1/(b+1) + b/r",block:true)
For b+1 iid keys, the number attaining the weak minimum lies between1 and1
plus all colliding unordered pairs. A pair collides with probability at
most2/r. The actual full normalized key separates infinity from affine
points and has at most2 points per key. This density/fiber argument is hand
analysis here; the formal probe checks symmetry and survival. A constant
key also satisfies survival while retaining everything.

*Input law.* Raw marker and shift arrays are independent; repeated samples
remain. Conditioning on auxiliary cleanliness needs its own argument.
Public random scalar multiples of a supplied subgroup generator can sample
uniform points mathematically, with their generation costs charged. No private
original scalar labels are used. Do not transfer continuous-CDF formulas.

#pagebreak()
#text(size:16pt,weight:"bold")[The construction cost still to remove]

*Explicit architecture, hand counts.* For four lists of size b, first form
two b² pair-subtotal families. Filtering both families against b shifts tests
2b³ translated points/keys. Charge markers, shifts, encodings, dictionary
work, duplicates, full provenance, recovery and final relation checks.
Streaming changes storage; it does not remove the raw tests. The ordinary
explicit four-color pair join takes O(b²) group additions plus its dictionary
or sort join. No speed gain is claimed for this shifted construction.

*Next constructive interface.* Given many centers Ua, raw shifts Tj and
threshold tau, report actual (a,j) with kappa(Ua+Tj)<=tau, using charged setup,
query, memory and output costs without testing every raw pair. Coordinate-aware
batching, its actual random-input yield and a witness extractor remain open.
A global zero relation makes the two root children opposite, not every
internal subtotal. Do not multiply this one-join bound through a deeper tree.

#table(columns:(2fr,3fr),inset:5pt,stroke:0.4pt,
  [Requested component],[Evidence / status],
  [Primitive provenance],[11 shared laws; same-tag contract retained],
  [Actual fixed-filter moments],[7 shared laws; raw independent uniform shifts],
  [Marker-rank survival],[10 shared laws; finite count including ties],
  [General prime-field assembly],[Actual points/subgroups; inherited laws],
  [Efficient implicit generation],[Open coordinate-aware translated-filter query],
  [Complete end-to-end algorithm],[Unmet; full construction, useful yield and recovery/cost missing],
)

*Evidence.* Lean4.35.0 / Mathlib cfc55fc. Source a078981 includes28 named
laws. Plans and inherited-law floors precede both new families. Pre-source
PCC102ac7/9ea735 remain unverified and their subjects frozen. Canonical gate001
audits205 theorems,0 failures,0 trusted-native exceptions; all28 named axiom
prints use only subsets of propext, Classical.choice and Quot.sound.
Failed floors, API probes and moment-build001 remain alongside passing
checks. No limit, trust, inventory or linter policy was weakened; warning
bytes are preserved. No fresh lean4checker result or hosted pass is asserted.

The original subexponential complete-algorithm target remains open. The
frozen numerical panel still requires checkpoint access. Crypto4311/4338/4352
frozen branches and separate resolvers were not extended by this owner study.
The diagram records the new proof and missing interface; canonical measured
graphs have no new value or completed-algorithm edge to update.

*Primary sources read.*
#link("https://people.eecs.berkeley.edu/~daw/papers/genbday.html")[Wagner, sections2–3];
#link("https://www.iacr.org/conferences/eurocrypt2010/talks/knapsacks.pdf")[Howgrave-Graham/Joux, slides9–14];
#link("https://faculty.washington.edu/yenchic/20A_stat512/Lec9_Order.html")[Chen, order statistics].
Scalar/modular filtering and continuous-input assumptions are not transferred
to field-coordinate generation. KB unavailable; BCJ full mirror inaccessible;
no novelty claim. Full proof maps, source table and raw receipts:
../auxiliary-shift-20261115.md.
