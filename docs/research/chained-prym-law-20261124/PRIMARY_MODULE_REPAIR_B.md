# Distinct module-interface repair B, after first A import failure

Official Lean reference section5.3--5.5 read, including module headers,
public visibility and serialized parts:
https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/ .
The public/private interface can avoid importing upstream proof bodies;
public sections expose theorem names. This changes packaging, not logic.
[pcc:unverified]

Lean community quickstart read, especially visibility and declarations:
https://leanprover-community.github.io/extras/module-system-quickstart.html .
Legacy non-module importers load transitively referenced private material.
Module importers use public interfaces unless explicitly importing all.
We need actual public homomorphism definitions and laws, not their private
implementation details. Keep both theorem types and proof steps unchanged.
[pcc:unverified]

Installed pinned Lean4.35 source Lean/Elab/Import.lean lines142--165 was
read: processHeaderCore selects exported level for module files and private
level for legacy files. Actual Mathlib Hom.Defs itself starts with module
and public imports. This justifies a genuinely distinct packaging repair
under unchanged2GiB120s1worker/default logic. No compatibility/private
warning suppression, theorem weakening, cache rebuild or runtime change.
[pcc:unverified]

First A dataa852b6: failed reading existing2995944B Lean private Simp/Main
file before theorem checking, no axiom audit. File digest0b00f72feb69725d...
is retained. This wording alone does not prove ENOMEM; the prior law34 H
trace's ENOMEM is a separate source/runtime-profile negative. Do not conflate
them or claim a missing file. No unchanged A compile rerun. [pcc:unverified]
