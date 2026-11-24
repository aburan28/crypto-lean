# Prospective actual odd-order point assembly

The generic cleared/unit tangent identities and actual polynomial product
residue laws now pass residue-direct003 with explicit constant-map rewrites.
Two earlier broad simplification attempts hit default200000-heartbeat whnf;
raw retained, no limit change. Monic actual002 passes after empty-constant
rewrite correction; initial actual001 failure retained.

Next hypothesis: assemble the residue law on actual Mathlib affine point-group
semantics. For W with a1=a2=a3=0, characteristic!=2, any nonzero P killed by
odd q has the public half R=[q/2+1]P and R+R=P. This half is finite and its
ordinate nonzero, because its double is nonzero. Actual slope/addX formulas
should then produce xP and a polynomial U with P.xRep=![xP,1] and

    f divides U^2-(C xP-X).

Acceptance: actual Point/nsmul/xRep/Equation/slope/addX semantics compile,
no hidden scalar, no assumed coordinate bridge in the final endpoint. Keep
identity/infinity and zero-ordinate exclusions explicit. The finite product
law then supplies residue witnesses for every selected collection of such
inputs; it supplies no polynomial-square quotient or zero-sum relation.
This targets the shortcut on the odd-order subgroup input regime. No field
instance or numerical/scientific/group search is executed; ordinary source
checks and all frozen evidence boundaries remain unchanged.
