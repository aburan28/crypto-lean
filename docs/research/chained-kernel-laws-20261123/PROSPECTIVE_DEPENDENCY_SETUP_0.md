# Phase0: pinned software dependencies only

Before any new formal source is compiled, materialize the exact dependency
revisions in the existing root lake-manifest. The library remains at Lean
4.35.0 and Mathlibcfc55fc58714a59dc06e6e79edc6d1d95140d3c2. No pin bump,
new provider, paid job, old consumer replay or locked-vault access.
[pcc:unverified]

The published shell source checks its complete flat source lock against the
actual public source commit before doing work. Pure Git clones fetch exactly
the manifest commits at depth1; they install software source, not experimental
data. Then the official pinned Mathlib cache command fetches only
Mathlib.Algebra.Group.Hom.Instances, Mathlib.Algebra.Field.ZMod and
Mathlib.LinearAlgebra.BilinearForm.Orthogonal plus their imports. Source
`Cache/Main.lean` at the pinned revision documents selective module arguments;
`Cache/IO.lean` documents MATHLIB_CACHE_DIR. Never use unsafe/fallback scopes,
an alternate Mathlib revision or a source build of Mathlib.
[pcc:unverified]

This phase may bootstrap the official cache utility; it runs no new study
law, native qualifier or consumer proof. Each dependency/cache command has a
600s setup timeout,2GiB virtual process cap and one worker. The later actual
proof/native phases retain their separately frozen120s/2GiB/one-worker limits
and default logical proof limits. Set the diagnosed smaller startup allocator
and runtime reservations before the first Lake process. This is software
setup, not a benchmark or replacement for an EKS-only research workload.
[pcc:unverified]

Retain whole stdout/stderr/exits and argv for every setup command, exact
source pins, tool hashes and distinct BUILD/POST manifests. Output/cache/tmp
directories must be fresh RAM paths; source/proof inputs stay unchanged.
First failure is retained before a versioned repair. Missing prebuilt cache
is infrastructure; no proof outcome follows. Whole large cache/log packets
remain temporary under artifact policy until ordinary CI or approved store
custody exists. Do not split, rename or inline-compress them to fit Git.
[pcc:unverified]
