# Projective Vélu coordinates

`CryptoLean.Polynomial.ProjectiveVelu` defines the ordinary ring pair
corresponding to x -> x+tau/(x-xi), using homogeneous polynomials
N=A^2-xi*A*B+tau*B^2 and D=A*B-xi*B^2. Its generic law proves that N,D
remain coprime whenever A,B are coprime and tau is a unit, over any CommRing.
In particular this applies to retained residues in polynomial quotient rings.

The proof uses Mathlib coprimality of powers, additive-multiple invariance,
and products. It opens the pair definition only in its owning step law to
expose those two polynomial expressions; no existing semantic pair operation
supplies that expression-specific fact. Polynomial rearrangements use ring.
No resources are raised, no new axioms or native proofs are used.

If a terminal N equals c*D, the existing `IsCoprime.isUnit_of_dvd` makes D a
unit. A finite terminal value therefore needs no separate inverse witness
for this projective circuit. This statement does not prove that a native
parser/generator implements the circuit, or a degree/yield bound for solving it.

The formulas are the degree-two case in crypto's native isogeny_eval/small_degree
and the existing PKM auxiliary-tower notes. First consumer: crypto study
research/projective_aux_norm_20261115. Its six-field instance map precedes
Lean edits. The actual quotient-ring assembly probe uses F19 and three public
steps (14,1),(16,5),(17,3); the native tower constants remain independently
checkable instance obligations, not hypotheses hidden by this generic law.
