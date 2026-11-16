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


def request_metadata(path):
    path = Path(path)
    if path.stat().st_size > 65536:
        raise ValueError("input exceeds 64KiB metadata cap")
    raw = path.read_bytes()
    config = json.loads(raw)
    if (not isinstance(config, dict) or not {"curve", "search"} <= set(config)
            or set(config) - {"curve", "search", "caps", "query_labels"}
            or not isinstance(config["curve"], dict) or not isinstance(config["search"], dict)):
        raise ValueError("unsupported/missing input envelope keys")
    caps = Caps.parse(config.get("caps", {}))
    return raw, caps


def capped_command(argv, stdout_path, stderr_path, caps, *,
                   wall_seconds=None, process_receipt=None):
    """Direct process-group deadline and limits for workers and replay alike."""
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
    process = None

    def terminate(signum, _frame):
        # The finally block kills the group, including after parent exit.
        raise SystemExit(128+signum)

    previous_handler = signal.signal(signal.SIGTERM, terminate)
    try:
        with Path(stdout_path).open("xb") as stdout, Path(stderr_path).open("xb") as stderr:
            process = subprocess.Popen(
                argv, stdout=stdout, stderr=stderr, preexec_fn=limits,
                start_new_session=True, env=env,
            )
            if process_receipt is not None:
                exclusive_json(process_receipt, {"pid": process.pid, "argv": argv})
            try:
                code = process.wait(timeout=caps.wall_seconds if wall_seconds is None
                                    else min(wall_seconds, caps.wall_seconds))
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
    finally:
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        signal.signal(signal.SIGTERM, previous_handler)
    return {"exit_code": code, "wall_timeout": timed_out,
            "elapsed_seconds": time.monotonic()-start}


def run_request(input_path, output_path, sage_name="sage"):
    """One direct worker process group, callable by the paired controller."""
    raw, caps = request_metadata(input_path)
    sage = shutil.which(sage_name)
    if sage is None:
        raise FileNotFoundError("Sage executable unavailable; no worker was launched")
    output = Path(output_path)
    output.mkdir(parents=True, exist_ok=False)
    output = output.resolve()
    frozen_input = output / "input.json"
    with frozen_input.open("xb") as stream:
        stream.write(raw)
    worker = Path(__file__).with_name("worker.py").resolve()
    sources = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
               for p in Path(__file__).parent.glob("*.py")}

    execution = capped_command(
        [sage, "--python", str(worker), "--input", str(frozen_input),
         "--output", str(output)], output / "stdout.log", output / "stderr.log", caps,
        process_receipt=output / "process.json",
    )
    # Each log has RLIMIT_FSIZE; worker artifacts share another output_mib.
    # An external EKS/container memory limit must bound the entire process tree.
    manifest = {
        "input_sha256": hashlib.sha256(raw).hexdigest(), "source_sha256": sources,
        "caps": caps.dictionary(), **execution,
        "worker_result_present": (output / "result.json").exists(),
        "output_contract": "two per-log limits plus one shared artifact limit",
        "memory_contract": "per-process address limit; container limit also required",
    }
    exclusive_json(output / "launcher.json", manifest)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sage", default="sage")
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.validate_only:
        raw, caps = request_metadata(args.input)
        print(json.dumps({"input_sha256": hashlib.sha256(raw).hexdigest(),
                          "caps": caps.dictionary(), "worker_executed": False,
                          "scope": "input envelope/resource metadata only"}))
        return
    manifest = run_request(args.input, args.output, args.sage)
    if manifest["wall_timeout"] or manifest["exit_code"] != 0:
        raise SystemExit(2)


if __name__ == "__main__":
    main()
