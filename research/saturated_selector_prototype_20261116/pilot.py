#!/usr/bin/env python3
"""UNEXECUTED paired known-answer pilot; no statistical yield claim."""

import argparse
from collections import Counter
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time


def command(argv, stdout, stderr, seconds):
    with stdout.open("xb") as out, stderr.open("xb") as err:
        process = subprocess.Popen(argv, stdout=out, stderr=err, start_new_session=True)
        try:
            return process.wait(timeout=seconds), False
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            return process.returncode, True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parent
    sage = shutil.which("sage")
    if sage is None:
        raise SystemExit("Sage unavailable; pilot not started")
    expected = json.loads((root / "fixtures" / "public17.expected.json").read_text())
    modes = {}
    started = time.monotonic()
    for mode in ("ordinary", "saturated"):
        case = root / "fixtures" / f"public17.{mode}.json"
        destination = args.output / mode
        # The controller's deadline includes both workers and replays.
        remaining = 360-(time.monotonic()-started)
        if remaining <= 0:
            modes[mode] = {"status": "controller_deadline"}
            break
        code, timeout = command(
            [sage, "--python", str(root / "launch.py"), "--input", str(case),
             "--output", str(destination)], args.output / f"{mode}.stdout.log",
            args.output / f"{mode}.stderr.log", min(150, remaining))
        result_path = destination / "result.json"
        result = json.loads(result_path.read_text()) if result_path.exists() else {}
        events_path = destination / "events.jsonl"
        events = [json.loads(line) for line in events_path.read_text().splitlines()
                  if line.strip()] if events_path.exists() else []
        methods = Counter(r.get("method", "missing") for r in result.get("relations", []))
        short_rows = sum(e["short_rows"] for e in events if e.get("stage") == "lll_verified")
        replay_code, replay_timeout = None, False
        if result.get("status") == "success":
            remaining = 360-(time.monotonic()-started)
            if remaining > 0:
                replay_code, replay_timeout = command(
                    [sage, "--python", str(root / "verify.py"), "--input", str(case),
                     "--result", str(result_path)], args.output / f"{mode}.replay.stdout.log",
                    args.output / f"{mode}.replay.stderr.log", min(30, remaining))
        modes[mode] = {
            "launcher_exit_code": code, "launcher_timeout": timeout,
            "worker_status": result.get("status", "no_result"),
            "short_rows": short_rows, "accepted_methods": dict(methods),
            "replay_exit_code": replay_code, "replay_timeout": replay_timeout,
            "known_answer_matches": result.get("status") == "success"
                and int(result["scalar"]) == expected["scalar"],
        }
    ordinary = modes.get("ordinary", {})
    saturated = modes.get("saturated", {})
    report = {
        "scope": "paired published toy known-answer control; no yield/speed/asymptotic claim",
        "modes": modes,
        "ordinary_control_contradiction": ordinary.get("short_rows", 0) > 0,
        "saturation_path_covered": saturated.get("accepted_methods", {}).get("saturated_lattice", 0) > 0,
        "saturation_scalar_replayed": saturated.get("replay_exit_code") == 0
            and saturated.get("known_answer_matches", False),
        "complete_algorithm_criterion_met": False,
    }
    with (args.output / "pilot-summary.json").open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")


if __name__ == "__main__":
    main()
