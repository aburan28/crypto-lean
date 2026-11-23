# C: unchanged official Lake entry through the pinned Lean frontend

B's synchronous-zero-worker proposal failed because Lake uses IO.Promise,
which needs an active task manager. Its full601566B trace is retained whole
with a hash/custody-pending record, and its first exit1 remains unchanged.
The trace also contains failed mappings; no single cause is isolated.
[pcc:unverified]

C uses a materially different startup path. The installed, unchanged
LakeMain.lean simply invokes Lake.cli. Run it via the exact pinned Lean
binary with explicit-j1, so the Lean shell applies the smaller stack settings
before its task manager is created. Keep one active worker rather than the
incompatible zero-worker fallback. All logical proof defaults,2GiB process
cap,600s setup deadline, dependency/cache pins and requested modules stay
unchanged. No new study law/consumer proof or old scientific qualifier runs.
[pcc:unverified]

Create a fresh private tool prefix: copy the complete original lean executable
byte-for-byte as bin/lean-real; symlink the unchanged lib/include/src and
other original tool binaries; install the two published thin shell frontends
as bin/lean and bin/lake. The Lean frontend rejects a different worker count;
the Lake frontend runs the unchanged official source. Lake's published
installation discovery uses the running executable's directory and co-located
bin/lean, so child compiler/Lake calls use the same bounded prefix. This
changes startup/orchestration only. No kernel binary, source, shared library,
type-checking rule, trust root or original installation is modified.
[pcc:unverified]

Pin/read back the external LakeMain source and original binaries/shared
libraries, compare the copied executable and shell templates before calls,
and retain distinct source/build/post guards. Verify the nine installed Git
revisions without cloning them again. The first C selective-cache command is
fully traced, with whole streams/exits preserved before any further repair.
Do not build Mathlib from source, choose unsafe cache scopes or treat a
frontend/cache success as a checked new mathematical proof. [pcc:unverified]
