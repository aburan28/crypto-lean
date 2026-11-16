# Fixed-filter moment implementation map

The prospective C plan/floor pinned by PCC102ac7 remain unchanged.
Mathlib has no integral-of-uniformOn named result in the bounded current
source search. Its existing integral_fintype instead exposes singleton
weights directly; uniformOn_univ gives the constant weight. This is the
same finite uniform counting obligation as the plan's indicator route,
with identical input law and target. No generic integration or variance
law is copied. Check this assembly floor before adding the new glue.

| Statement | Kind | Owner | Structure / inherited laws |
|---|---|---|---|
| shifted-hit mean | law/glue | Group.ShiftMoments | finite discrete AddCommGroup; integral_fintype, uniformOn_univ, Equiv.addLeft.sum_comp, sum_boole |
| shifted-hit variance | endpoint | Group.ShiftMoments | variance_eq_sub, indicator squared equals itself |
| actual real count interface | law/interface | Group.ShiftMoments | acceptedCount_eq_sum plus Nat.cast_sum |
| pool mean | endpoint | Group.ShiftMoments | integral_sum, integral_comp_eval, shifted-hit mean |
| pool variance | endpoint | Group.ShiftMoments | variance_sum_pi unchanged |
| pool second raw moment | endpoint | Group.ShiftMoments | variance_eq_sub plus previous endpoints and ring arithmetic |
| prime-field probe | instance/endpoint | receipt | actual finite subgroup, same unmodified endpoints |

For the pool count, use the actual function T -> (acceptedCount U V S T : R).
The real-valued interface is obtained from the existing natural-valued
count law; no new independent-gates hypothesis. Open acceptedCount nowhere
else. Raw Measure.pi of uniformOn univ, fixed S=-S and U+V=0 remain explicit.

The moment arithmetic is exactly k*delta, k*delta*(1-delta), and
k*delta+k*(k-1)*delta^2 with the subtraction in R. Moment values and costs
are separate; these laws do not supply a fast generator.
