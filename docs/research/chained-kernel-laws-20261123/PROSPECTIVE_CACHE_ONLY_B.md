# B: cache-only continuation with the synchronous task fallback

All nine package source stages completed in setup0 and must not be rerun.
Its cache command remains an abort134 with empty phase output; first raw
streams and source guards are public at59480f3. No study proof ran.
[pcc:unverified]

Tagged Lean4.35 runtime/object.cpp reads LEAN_NUM_THREADS. A value0 leaves
the asynchronous task manager absent, and lean_task_spawn_core then runs the
closure synchronously. Generated LakeMain initializes the task manager before
lean_run_main, while the thread-stack environment is handled in the latter
runtime entry path. Thus the prior one-worker environment does not ensure
early worker stacks use the later smaller-stack setting. This is a
source-supported startup diagnosis, not a trace of setup0's unobserved mmap.
Lake has no -j CLI option; do not invent one. [pcc:unverified]

B requests LEAN_NUM_THREADS=0, making runtime tasks synchronous on the main
thread; this tightens the original one-worker bound. Keep the same2GiB cap,
600s software-setup timeout, smaller allocator/runtime settings and exact
manifest/cache arguments. It verifies the nine already-installed revisions
and resumes only the first unfinished official prebuilt-cache phase. Pin the
five actual Lean/Lake shared libraries in addition to compiler binaries.
Run the first B cache call under a full clone/mmap/exec trace. Preserve all
raw bytes and first exits; no stderr text is invented for setup0.
[pcc:unverified]

This still runs no study theorem, consumer assembly or old native qualifier.
No Mathlib source build, unsafe cache scope, pin bump, trust/gate change,
paid compute or vault access. Complete large trace/cache packets remain
whole and temporary pending ordinary CI/store custody. The general proof
and the instance-gate assembly remain open until their actual future calls.
[pcc:unverified]
