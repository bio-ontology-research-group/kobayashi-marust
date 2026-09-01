#!/usr/bin/env python3
"""Regression tests for fail-closed native taxonomy fingerprinting."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "runners" / "full_iri_fingerprint.py"
VALIDATE = Path(__file__).parents[1] / "runners" / "validate_result.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class FullIriFingerprintTest(unittest.TestCase):
    def run_fingerprint(self, output_text: str) -> dict:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source.ofn"
            output = root / "taxonomy.owlxml"
            source.write_text(
                "Ontology(\nDeclaration(Class(<urn:test:A>))\n)\n", encoding="utf-8"
            )
            output.write_text(output_text, encoding="utf-8")
            completed = subprocess.run(
                [sys.executable, str(SCRIPT), "--input", str(output), "--format", "owlxml",
                 "--source-ontology", str(source), "--output-prefix", str(root / "fp")],
                check=True, capture_output=True, text=True,
            )
            return json.loads(completed.stdout)

    def test_reports_source_class_missing_from_empty_taxonomy(self) -> None:
        record = self.run_fingerprint("<Ontology></Ontology>\n")
        self.assertEqual(record["ontology_declarations"], 1)
        self.assertEqual(record["output_declarations"], 0)
        self.assertEqual(record["missing_source_declarations"], 1)

    def test_accepts_taxonomy_that_declares_source_class(self) -> None:
        record = self.run_fingerprint(
            '<Ontology><Declaration><Class IRI="urn:test:A"/></Declaration></Ontology>\n'
        )
        self.assertEqual(record["missing_source_declarations"], 0)

    def test_validator_rejects_empty_konclude_taxonomy(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source.ofn"
            runtime = root / "konclude"
            runner = root / "runner.py"
            output = root / "case.taxonomy.owlxml"
            stderr = root / "case.stderr"
            source.write_text("Ontology(\nDeclaration(Class(<urn:test:A>))\n)\n", encoding="utf-8")
            runtime.write_bytes(b"runtime")
            runner.write_bytes(b"runner")
            output.write_text("<Ontology></Ontology>\n", encoding="utf-8")
            stderr.write_bytes(b"")
            fingerprint = subprocess.run(
                [sys.executable, str(SCRIPT), "--input", str(output), "--format", "owlxml",
                 "--source-ontology", str(source), "--output-prefix", str(root / "case.fingerprint")],
                check=True, capture_output=True, text=True,
            )
            fp = json.loads(fingerprint.stdout)
            result = {
                "schema": 1, "baseline": "konclude", "ontology_id": "case",
                "ontology_sha256": digest(source), "input_ontology_sha256": digest(source),
                "binary_sha256": digest(runtime), "runner_sha256": digest(runner),
                "status": "ok", "checkpointed": True, "wall_s": 1.0, "peak_mb": 1.0,
                "rc": 0, "stderr_sha256": digest(stderr), "consistency": "true",
                "subsumptions": fp["subsumptions"], "unsatisfiable": fp["unsatisfiable"],
                "taxonomy_sha256": fp["taxonomy_sha256"],
                "relation_sha256": fp["relation_sha256"], "output_sha256": digest(output),
            }
            result_path = root / "case.result.json"
            result_path.write_text(json.dumps(result), encoding="utf-8")
            checked = subprocess.run(
                [sys.executable, str(VALIDATE), "--result", str(result_path),
                 "--baseline", "konclude", "--ontology-id", "case", "--ontology", str(source),
                 "--runtime", str(runtime), "--runner", str(runner)],
                capture_output=True, text=True,
            )
            self.assertNotEqual(checked.returncode, 0)
            self.assertIn("omits source class declarations", checked.stderr)


if __name__ == "__main__":
    unittest.main()
