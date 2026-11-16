"""Generic launcher/process controls using a fake client, never Sage/curves."""

import json
from pathlib import Path
import tempfile
import unittest

from launch import run_request


class LauncherControls(unittest.TestCase):
    def case(self, root):
        path = root / "metadata-input.json"
        path.write_text(json.dumps({"curve": {}, "search": {}, "caps": {
            "wall_seconds": 1, "cpu_seconds": 2, "memory_mib": 256, "output_mib": 1}}))
        return path

    def fake(self, root, body):
        path = root / "fake-client"
        path.write_text("#!/usr/bin/env python3\n" + body)
        path.chmod(0o700)
        return str(path)

    def test_missing_runtime_does_not_create_output(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            with self.assertRaises(FileNotFoundError):
                run_request(self.case(root), root / "output", str(root / "missing"))
            self.assertFalse((root / "output").exists())

    def test_existing_evidence_is_never_overwritten(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            destination = root / "output"
            destination.mkdir()
            marker = destination / "marker"
            marker.write_text("preserve")
            with self.assertRaises(FileExistsError):
                run_request(self.case(root), destination, self.fake(root, "raise SystemExit(7)\n"))
            self.assertEqual(marker.read_text(), "preserve")

    def test_wall_deadline_stops_the_direct_worker_group(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            fake = self.fake(root, """import pathlib, subprocess, sys, time
out = pathlib.Path(sys.argv[sys.argv.index('--output')+1])
child = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])
(out/'fake-child.pid').write_text(str(child.pid))
time.sleep(30)
""")
            result = run_request(self.case(root), root / "output", fake)
            self.assertTrue(result["wall_timeout"])
            self.assertNotEqual(result["exit_code"], 0)
            self.assertFalse(result["worker_result_present"])
            child = int((root / "output/fake-child.pid").read_text())
            stat = Path(f"/proc/{child}/stat")
            if stat.exists():
                self.assertEqual(stat.read_text().split()[2], "Z")


if __name__ == "__main__":
    unittest.main()
