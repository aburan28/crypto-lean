# Grouped endpoint ports and replicated packet vertices

`CryptoLean.Combinatorics.PortMass` composes existing Mathlib multiset
counting laws. For a finite label type G, an edge multiset E in G×G,
old vertex labels V, and natural p and P, its three laws give:

```
sum_g (count_g(map fst E) + count_g(map snd E)) = 2 card(E)
sum_g (count_g(map fst E) + count_g(map snd E)) p = 2 card(E) p
sum_g (count_g(V) + P) = card(V) + card(G) P
```

The first two count endpoint incidences with multiplicity; parallel edges
are retained. The last counts every old vertex once and replicates the
constant packet description in every group, including zero-port groups.
These are structural accounting laws. A consumer must separately establish
packet coverage, endpoint/label extraction, and what its constructor actually
allocates. The common weight p does not measure bit operations. [pcc:unverified]

The proof applies `Multiset.sum_count_eq_card` as stated, then uses existing
`count_add`, `card_add`, `card_map`, `count_nsmul`, `card_nsmul` and finite
constant-sum laws. Multiplying a multiset in the weight proof is a proof device;
it does not prescribe allocating p copies in the implementation. No graph
wrapper, custom axiom or new counting method is introduced. [pcc:unverified]

Focused qualification uses official Lean4.35.0 and retained Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The unchanged proof gate
audits all three shared theorems with zero failures and zero trusted native
proofs; a consumer of all three laws passes official
`leanchecker --fresh PortControls`. All six shared/consumer axiom queries
list only propext, Classical.choice and Quot.sound. See the retained
[gate log](checks/port-mass-20261123/shared-audit.log),
[axiom output](checks/port-mass-20261123/axioms.txt) and
[phase receipt](checks/port-mass-20261123/qualification.json).
These are unsigned producer observations. [pcc:unverified]

The repository's default Mathlib pin remains
`cfc55fc58714a59dc06e6e79edc6d1d95140d3c2`. The complete source file
owning `sum_count_eq_card` is identical at both pins, but transitive sources
differ. This focused56 qualification is **not** a default-cfc or whole-library
qualification. Neither dependency pin, toolchain, gate nor elaboration/resource
limit was changed. Earlier failed attempts remain in the consumer study.
[pcc:unverified]

Consumer: [crypto PR5046](https://github.com/isogeny-labs/crypto/pull/5046),
`research/hashed_ecdl_port_mass_20261123`. Its forced native constructor
controls bind actual packet/port/vertex objects separately from the theorem.
Source review is written same-team review, not independent execution.
KB was unavailable; exact Mathlib/source inspection and bounded repository
searches provide no novelty clearance. The laws reuse established counting.
[pcc:unverified]
