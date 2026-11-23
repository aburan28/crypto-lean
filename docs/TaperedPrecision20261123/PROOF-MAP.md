# Instance gate, ownership and fidelity

1. Structure above: standard Nat arithmetic/order, exact floor division and
   natural powers from Lean/Std. No replacement semantic objects.
2. Existing laws: Nat.div_mul_le_self; Nat.le_mul_of_pos_right;
   Nat.lt_two_pow_self; Nat.pow_le_pow_right; Nat.pow_add; Nat.mul_le_mul;
   Nat.add_le_add; associativity/commutativity. Used as stated.
3. Instance: the source's integer precision formula, active cumulative
   exponent a=A+2u, and explicit inherited/dimensional budgets.
4. Assembly: the Std probe type-checks the exact laws; the canonical module
   was copied/frozen before compilation, followed by a separate axiom query.
   The earlier Mathlib assembly separately checks the path's geometric-sum
   floor, not the whole path theorem.
5. Missing consumer components: bind real call history to an inherited
   coefficient; derive/check dimension absorption from source guards; prove
   packet/mode, retained-allocation and entry-work refinements. Not supplied
   as axioms or assumed theorem conclusions.
6. Inheritance: all scalar operations inherit Std Nat instances; order
   inequalities use the existing named laws; the one defining expansion is
   `childPrecision_formula`, and the other laws rewrite through it.

Declaration order: source expression; defining expansion; increment bound;
conditional scalar bound; only then the study's numerical controls. These are
shared source resource laws in their owner, not copies for individual curves.

| Statement | Kind / owner | Exact scope and missing bridge |
| --- | --- | --- |
| childPrecision_formula | source-model equality / Core | rfl expansion of the literal arithmetic; no Rust compiler/refinement theorem |
| increment_le | resource law / Core | all Nat dimensions, positive u<=M; one increment only |
| childPrecision_mul_le | resource law / Core | six explicit premises, including inherited bound and both dimensional absorption inequalities; no proof of those premises for every call history |

| Report sentence | Lean endpoint | Difference from a general D.11/counter claim |
| --- | --- | --- |
| One increment <=40M2^a | increment_le | exact finite source expression under positive u<=M; no total bit-work claim |
| Current precision <=34MD/u | childPrecision_mul_le | multiplied-through inequality; conditional on the stated inherited/root/absorption premises; neither full history nor source-to-code refinement is proved |

Pinned runtime: Lean4.35.0, kernel commit
eb6cafb7290e8bd5f2937522d8d804f58f02bafc. Upstream baseff61cae,
its toolchain and Mathlibcfc55fc5 unchanged. This module is Std-only; the
different cached Mathlib56a00585 used for a separate anonymous assembly probe
does not enter its import closure. No library pin is changed to fit a proof.

Managed512MiB import-loader failures, root-path setup error, and earlier
typing diagnostics are retained in the consumer's development history.
Final focused builds use the same physical whole-cgroup15,032,385,536-byte
stop, one worker and600-second original phase deadline, with the separate
managed loader cap disabled. No elaboration heartbeat/recursion limit changed.
