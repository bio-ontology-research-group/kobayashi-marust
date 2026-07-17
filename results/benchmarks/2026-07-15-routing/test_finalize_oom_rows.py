#!/usr/bin/env python3
"""Contract tests for evidence-gated production OOM finalization."""

import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "finalize_oom_rows", HERE / "finalize_oom_rows.py"
)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FinalizeOomRowsTest(unittest.TestCase):
    def test_records_binary_and_runner_identity_after_explicit_oom(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "onts.txt").write_text("ore_ont_1.owl\n", encoding="utf-8")
            (root / "slurm").mkdir()
            (root / "slurm" / "prod-42_0.out").write_text(
                "error: Detected 1 oom_kill event in StepId=42.batch\n",
                encoding="utf-8",
            )
            binary = root / "km"
            runner = root / "runner.py"
            binary.write_bytes(b"immutable-km")
            runner.write_bytes(b"immutable-runner")
            argv = [
                "finalize_oom_rows.py",
                "--root",
                os.fspath(root),
                "--tag",
                "candidate",
                "--binary",
                os.fspath(binary),
                "--runner",
                os.fspath(runner),
                "--worker-job",
                "42",
                "--indices",
                "0",
            ]
            with mock.patch.object(sys, "argv", argv):
                MODULE.main()
            result = root / "production-sweeps/candidate/results/ore_ont_1.owl.jsonl"
            row = json.loads(result.read_text(encoding="utf-8"))
            self.assertEqual(row["binary_sha256"], MODULE.sha256(binary))
            self.assertEqual(row["runner_sha256"], MODULE.sha256(runner))
            self.assertTrue(row["finalized_from_slurm_oom"])

    def test_refuses_missing_oom_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "onts.txt").write_text("ore_ont_1.owl\n", encoding="utf-8")
            (root / "slurm").mkdir()
            (root / "slurm" / "prod-42_0.out").write_text(
                "NO-ROW ontology=ore_ont_1.owl rc=137\n", encoding="utf-8"
            )
            binary = root / "km"
            runner = root / "runner.py"
            binary.write_bytes(b"km")
            runner.write_bytes(b"runner")
            argv = [
                "finalize_oom_rows.py",
                "--root",
                os.fspath(root),
                "--tag",
                "candidate",
                "--binary",
                os.fspath(binary),
                "--runner",
                os.fspath(runner),
                "--worker-job",
                "42",
                "--indices",
                "0",
            ]
            with mock.patch.object(sys, "argv", argv):
                with self.assertRaisesRegex(SystemExit, "no Slurm OOM evidence"):
                    MODULE.main()


if __name__ == "__main__":
    unittest.main()
