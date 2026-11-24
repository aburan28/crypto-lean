# Prospective actual-input discriminator for the cubic residue shortcut

Monic owner source direct002 and owner-build001 pass; first actual application
check failed only an over-unfolded empty-constant simp goal, raw retained.
This new mathematics attempt tests the discarded cubic quotient shortcut on
structured curve inputs, beyond the earlier symbolic nonsplit counterexample.

For a short-curve affine point R=(r,s), s!=0, slope m with2s*m=3r²+a,
the doubled abscissa is xP=m²-2r. Prediction: modulo f=X³+aX+b,

    xP-X = (m-(X²+rX+r²+a)/s)^2.

More precisely, the difference of the square and xP-X should equal
f*(X+2r)/s². Prove a cleared identity first over CommRing using actual curve
s²=r³+ar+b and tangent equations, then a unit-inverse identity and actual
polynomial divisibility over any field. Products of these residues should
remain squares modulo f for ANY selected collection of such doubled points.

HAND original-input bridge: in an odd-prime-order subgroup every P has a
publicly computable half R=[(q+1)/2]P, so for nonidentity finite inputs the
cubic square-congruence is automatically satisfiable for every colored choice.
This does not require solving ECDLP. Actual Mathlib group-coordinate/halving
assembly remains separate unless compiled explicitly. Exclude s=0 in the
unit division; identity/infinity and2-torsion branches remain obligations.

Acceptance/falsification: generic ring identity, actual polynomial residue
and product laws compile with symbolic applications, default limits/standard
axioms only. A failure narrows this discriminator. A successful identity
rejects bare cubic-residue testing as a useful filter on doubled-coordinate
inputs; it does not reject full polynomial-square quotient or all selectors.
No numeric curve/field instance, scientific control or paid/native execution.
Raw receipts belong to the current monic phase; all406 older pins/22rows stay
frozen. This adds a NEW source file, never modifies pinned norm modules.
