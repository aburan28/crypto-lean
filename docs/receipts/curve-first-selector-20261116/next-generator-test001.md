# Next distinct-generator discriminator (not executed)

The hand factor count in docs/curve-first-selector-20261116.md redirects generic
models away from multiples of one S3 polynomial. Test a provenance-preserving
elimination of b between DISTINCT adjacent generators before another selector.
No implementation, symbolic compiler check, numerical or paid run for this
successor is claimed here. [pcc:unverified]

For a triple define A=x+y+z, B=xy+xz+yz, C=xyz. The identity to check against
the S3 owner is F=(B-a)^2-4A(C+b). Two such equations have the b-free combination

    G=A2*F1-A1*F2
     =A2*(B1-a)^2-A1*(B2-a)^2-4*A1*A2*(C1-C2).

For rational/projective triples with common denominator product Di and cleared
elementary numerators Ai,Bi,Ci, use

    Fi=(Bi-a*Di)^2-4*Ai*(Ci+b*Di), Zi=Ai*Di;
    G=Z2*F1-Z1*F2
     =A2*D2*(B1-a*D1)^2-A1*D1*(B2-a*D2)^2
       -4*A1*A2*(D2*C1-D1*C2).

Use actual generators from one original decomposition; no planted equal-sum,
equal-denominator or offset condition. Retain F1 and all Gi, not Gi alone.
On Z1!=0, F1=Gi=0 implies Fi=0 by Fi=(Zi*F1-Gi)/Z1. Handle Z1=0 and every
denominator/infinity branch separately; no original solutions may be dropped.
For distinct irreducibles and suitable coprimality, G avoids a forced F1 factor;
check this for the actual charted instance rather than assuming it.
[pcc:unverified]

Competing outcomes: lower coefficient/selector cost after b cancellation;
larger projective degree/height destroys the gain; or nonfinite/degenerate fibres
prevent useful recovery. Affine total degree alone is not enough: cleared
weights, all profiles, shifts, exceptional branches and original provenance
must be charged. Cancellation of b does not remove a or chart offsets.

Smallest next source obligations:

1. Generic symmetric S3 and cleared two-generator identities; no field numeric.
2. Exact equivalence with the retained F1 after localizing at Z1, including the
   missing branch; original target is still the fixed input curve.
3. Actual adjacent-chain projective support and weighted-L1 cost; compare with
   the original family before implementing. Explicit useful-root/fibre test.

Only continue to a selector driver if these provide a plausible charged-cost
improvement. A future numerical test needs its own frozen inputs and the existing
budget/runtime/image/caller/capacity/custody admission. The complete prime-field
ECDLP algorithm criterion remains unmet. [pcc:unverified]
