# Generic doubled-point law: instance and fidelity plan

Tracked by ACTIVE-only324a56596 and draft34. Consumer studies crypto4992 and
4997 retain their existing finite proof/source/raw records unchanged. This
document is prospective; no new proof or assembly build has run.
[pcc:unverified]

## Six fields before formal source

1. **Structure above:** Mathlib `AddMonoid`, additive homomorphisms, then
   inherited additive groups of `ZMod4 x ZMod2 x ZMod2`. The concrete product
   is a parameter/instance, not a new operation-record algebra.
2. **Theorem used as stated:** `map_add` and `map_zero` supply covariance
   and identity preservation. The missing proposed generic component says:
   if every double is either0 or p, p is itself a double, and F is an
   injective additive endomorphism, then F fixes p. We have not found an
   exact shared declaration in the inspected source/search scope; this is
   not a global absence claim. Build that reusable law here before its
   concrete consumer. Nonzeroness of p belongs to the subsequent fixed-point
   obstruction, not to the more general fixed-point law.
3. **Object as instance:** ordinary Mathlib product additive groups. The
   concrete candidate is p=(2,0,0), doubled from(1,0,0). The old consumer's
   custom Bool carrier is not silently identified with this product; its
   exact comparison/transport remains an explicit consumer bridge.
4. **Assembly probe:** after dependencies exist, compile the exact generic
   statement and a concrete product endpoint with the doubled-range and
   witness obligations. The initial probe/build is a separately frozen
   source-first call. It has not run yet; the design cannot claim an earned
   instance-gate receipt before that call.
5. **Missing components only:** generic unique-doubled-point law, concrete
   inherited product obligations, checked endpoint and optional exact old
   Bool-carrier bridge. The general geometric kernel classification/Picard
   quotient/descent bridge is outside these point-group modules.
6. **Inheritance:** zero/addition/group laws/decidable equality/finite carrier
   come from existing Mathlib product/ZMod instances; F's zero/addition laws
   come from `AddMonoidHom`; injection is an explicit hypothesis. No new
   field/group operation, trust override or mathematical resource override.

## Dependency and statement order

Phase0 only installs the exact manifest source and selected official prebuilt
Mathlib cache. Never build Mathlib from source. Then, before formal calls,
publish the actual generic module and assembly/consumer source, its complete
caller/source/dependency closure and first-call conditions. Build the generic
law first, its concrete instance next, then inspect actual axiom output and
run the canonical gate/auditor at the earned scope. Do not hide an absent
cache or a whole-project gate failure behind a successful focused build.
[pcc:unverified]

| Statement | Kind and owner | Hypotheses and intended conclusion |
| --- | --- | --- |
| Homomorphism fixes the represented doubled point | New generic law, CryptoLean.Group | Arbitrary inherited AddMonoid; doubled range contained in{0,p}; p in range; additive injective F; conclusion F(p)=p |
| Nonzero fixed-point consequence | Generic corollary or consumer endpoint | Same contracts plus p!=0; fixed-only-zero assumption gives contradiction |
| Product-group component | Instance obligation/endpoint, consumer example | ZMod4 x ZMod2 x ZMod2 with inherited operations; actual finite doubled-range/witness/nonzero obligations |
| Actual geometric double-Richelot obstruction | Written consumer result | Classification and Galois/abelian-variety realization are not supplied by the group law |

## Proof chain and competing controls

Choose x with x+x=p. By the existing map_add law,
F(p)=F(x)+F(x). The doubled-range contract makes this either0 or p.
In the zero case, map_zero and injectivity give p=0, so F(p)=p as well.
The nonzero obstruction then follows by applying a fixed-only-zero assumption
to p. No premise restates F(p)=p. [pcc:unverified]

Protect the contracts with separate explicit checks: if injection is dropped,
the zero endomorphism need not fix nonzero p; if p need not lie in the
doubled image, an elementary2-group and a moving endomorphism can violate
the claimed conclusion. The p=0 degenerate case is allowed in the generic
law. Use concrete inherited groups for sanity instances, not random trials
or a new mathematical engine. [pcc:unverified]

## Fidelity and source review

The generic point-group theorem concerns a homomorphism on actual inherited
algebraic structures; it does not certify a geometric isogeny or DLP solver.
The concrete product endpoint is stronger in semantic structure than the
earlier custom Bool operations, but no unchecked representation equivalence
is claimed. Each final claim must list exact hypotheses, declaration text,
dependency revision, build/gate and axiom receipts. [pcc:unverified]

Sources: existing `CryptoLean/Group/Torsion.lean` (homomorphism factorization),
`CryptoLean/Group/BilinearSketch.lean` (inherited group/ZMod instances),
library `docs/DESIGN.md`, consumer two-hop written argument and its exact
finite bindings, Mathlib's existing homomorphism interface at pinned
cfc55fc58714a59dc06e6e79edc6d1d95140d3c2. KB/lean-lsp tools are absent;
connected source searches and exact Git files are the recorded fallback.
No source absence or novelty clearance is asserted. [pcc:unverified]

Required skills read: workspace lean-instance-gate blob7d3ffa79 and
lean-prove blob5ff2df93. Default logical limits, no sorry/admit/new axiom/
native_decide, one Lake process at a time. A missing field remains open
until actually built; do not replace it with an assumed conclusion.
[pcc:unverified]
