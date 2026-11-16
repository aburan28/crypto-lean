#!/usr/bin/env python3
"""Capped launcher for an UNEXECUTED Sage research prototype.

No worker is run by importing this module or by requesting --help.
Use the existing execution/admission rules before running a numerical job.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import shutil
import signal
import subprocess
import time

from metadata import Caps


def exclusive_json(path, value):
    with Path(path).open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sage", default="sage")
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.input.stat().st_size > 65536:
        parser.error("input exceeds 64KiB metadata cap")
    raw = args.input.read_bytes()
    config = json.loads(raw)
    if not isinstance(config, dict) or set(config) - {"curve", "search", "caps", "query_labels"}:
        parser.error("unsupported input keys")
    caps = Caps.parse(config.get("caps", {}))
    if args.validate_only:
        print(json.dumps({"input_sha256": hashlib.sha256(raw).hexdigest(),
                          "caps": caps.dictionary(), "worker_executed": False}))
        return
    sage = shutil.which(args.sage)
    if sage is None:
        parser.error("Sage executable unavailable; no worker was launched")
    args.output.mkdir(parents=True, exist_ok=False)
    args.output = args.output.resolve()
    frozen_input = args.output / "input.json"
    with frozen_input.open("xb") as stream:
        stream.write(raw)
    worker = Path(__file__).with_name("worker.py").resolve()
    sources = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in Path(__file__).parent.glob("*.py")}

    def limits():
        resource.setrlimit(resource.RLIMIT_CPU, (caps.cpu_seconds, caps.cpu_seconds))
        memory = caps.memory_mib * 1024**2
        resource.setrlimit(resource.RLIMIT_AS, (memory, memory))
        output = caps.output_mib * 1024**2
        resource.setrlimit(resource.RLIMIT_FSIZE, (output, output))

    env = dict(os.environ)
    env.update(OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1", SAGE_NUM_THREADS="1")
    start = time.monotonic()
    timed_out = False
    with (args.output / "stdout.log").open("xb") as stdout, \
            (args.output / "stderr.log").open("xb") as stderr:
        process = subprocess.Popen(
            [sage, "--python", str(worker), "--input", str(frozen_input),
             "--output", str(args.output)], stdout=stdout, stderr=stderr,
            preexec_fn=limits, start_new_session=True, env=env,
        )
        try:
            code = process.wait(timeout=caps.wall_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            code = process.wait()
    # Each log has RLIMIT_FSIZE; worker artifacts share another output_mib.
    # An external EKS/container memory limit must bound the entire process tree.
    exclusive_json(args.output / "launcher.json", {
        "input_sha256": hashlib.sha256(raw).hexdigest(), "source_sha256": sources,
        "caps": caps.dictionary(), "exit_code": code, "wall_timeout": timed_out,
        "elapsed_seconds": time.monotonic() - start,
        "worker_result_present": (args.output / "result.json").exists(),
        "output_contract": "two per-log limits plus one shared artifact limit",
        "memory_contract": "per-process address limit; container limit also required",
    })
    if timed_out or code != 0:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
