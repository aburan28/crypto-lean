# H: native Lean late shell worker, unchanged proof and bounds

G Init loads; legacy and both module Mathlib controls fail1 with observed
ENOMEM. A module-visibility-only remedy is refuted. Every trace also contains
a successful1073745920B mapping followed by a later small worker stack.
Full raw streams/exits/trace hashes and source guards are retained; whole
large traces remain private/store-pending. [pcc:unverified]

New targeted hypothesis: native Lean can avoid an early default one-GiB
worker reservation while preserving a positive later shell task manager.
Pinned object.cpp blob9ed90394 reads LEAN_NUM_THREADS in early initialization;
zero leaves that manager absent. Unlike bundled Lake's CLI, the native Lean
shell has an explicit-j1 setting and constructs scoped_task_manager from
that setting after set_thread_stack_size_from_env (util/shell.cpp29b85988,
thread.cpp19bc8121). The constructor is visible in the exact object.cpp.
Those tagged source bodies were inspected before H. The earlier Lake-B
promise failure stays a failure; no Lake call is repeated. [pcc:unverified]

H changes only early LEAN_NUM_THREADS to0 in the F direct-Lean caller.
Each actual Lean command still uses-j1, allowing one late shell worker with
the already frozen smaller stack setting. The law, concrete instance,
controls, canonical auditor, libraries, pins, two-GiB/120second phase bounds
and default logical limits remain byte-identical. No trust/axiom/native
hook/resource override. This is a source-supported proposal, not a cause or
success assertion. [pcc:unverified]

Run generic law first, actual inherited product/control assembly second,
then unchanged canonical focused axiom auditor, all at fresh
/dev/shm/law34-proofH and /dev/shm/law34-proofH-tmp. Trace each phase's complete
mmap/open/clone activity to test the reservation prediction. Preserve every
first exit/stream/guard/whole-trace hash. Success still requires all three
phases0, matching guards and no nonstandard axioms; any startup/promise,
proof or audit failure is retained before a separately published successor.
This is not the whole-project gate or a signed PCC verdict. Publish full
source/readback before calls. [pcc:unverified]
