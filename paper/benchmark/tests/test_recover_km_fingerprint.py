import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "recover_km_fingerprint.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class RecoverKmFingerprintTest(unittest.TestCase):
    def test_recovery_is_source_and_output_bound(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "x.ofn"; source.write_text("Ontology(<x>)\n")
            taxonomy = root / "x.taxonomy.json"; taxonomy.write_text("{}\n")
            fingerprinter = root / "fingerprinter.py"; fingerprinter.write_text("# exact tool\n")
            nodes = root / "recovery.nodes.tsv.gz"; nodes.write_bytes(b"nodes")
            unsat = root / "recovery.unsat.txt.gz"; unsat.write_bytes(b"unsat")
            receipt = {
                "status": "ok", "algorithm": "km-json-sparse-scc-closure-fingerprint-v1",
                "input_sha256": digest(taxonomy), "source_ontology_sha256": digest(source),
                "node_fingerprints_sha256": digest(nodes),
                "unsatisfiable_names_sha256": digest(unsat),
                "taxonomy_sha256": "a" * 64, "relation_sha256": "b" * 64,
                "consistent": True, "subsumptions": 3, "unsatisfiable": 0,
                "wall_s": 1.2, "peak_mb": 4.0,
            }
            (root / "recovery.json").write_text(json.dumps(receipt))
            result = root / "x.result.json"
            result.write_text(json.dumps({
                "baseline": "km", "ontology_id": "x", "status": "fingerprint_error",
                "checkpointed": True, "rc": 0, "slurm_array_job_id": "123",
                "ontology_sha256": digest(source), "wall_s": 9.0, "peak_mb": 10.0,
            }))
            command = [
                sys.executable, str(SCRIPT), "--result", str(result),
                "--taxonomy", str(taxonomy), "--source-ontology", str(source),
                "--recovery-prefix", str(root / "recovery"),
                "--fingerprinter", str(fingerprinter), "--expected-array-job-id", "123",
                "--fingerprint-job-id", "456", "--differential-job-id", "789",
            ]
            subprocess.run(command, check=True, capture_output=True, text=True)
            recovered = json.loads(result.read_text())
            self.assertEqual(recovered["status"], "ok")
            self.assertEqual((recovered["wall_s"], recovered["peak_mb"]), (9.0, 10.0))
            self.assertTrue(recovered["fingerprint_recovery"]["reasoner_output_unchanged"])
            self.assertEqual(recovered["output_sha256"], digest(taxonomy))
            receipt["input_sha256"] = "0" * 64
            (root / "recovery.json").write_text(json.dumps(receipt))
            result.write_text(json.dumps({
                "baseline": "km", "ontology_id": "x", "status": "fingerprint_error",
                "checkpointed": True, "rc": 0, "slurm_array_job_id": "123",
                "ontology_sha256": digest(source), "wall_s": 9.0, "peak_mb": 10.0,
            }))
            failed = subprocess.run(command, capture_output=True, text=True)
            self.assertNotEqual(failed.returncode, 0)
            self.assertIn("input digest mismatch", failed.stderr)


if __name__ == "__main__":
    unittest.main()
