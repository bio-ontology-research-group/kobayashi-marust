import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("audit_submission_readiness.py")
SPEC = importlib.util.spec_from_file_location("audit_submission_readiness", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


class CurrentOboReadinessTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.old_root = MODULE.ROOT
        MODULE.ROOT = self.root
        self.final = self.root / "benchmark" / "generated" / "current-final"
        self.final.mkdir(parents=True)
        aggregate = b'{"schema":1}\n'
        records = b"0" * 64 + b"  current-results/km/example.result.json\n"
        tex = (b"% Generated from aggregate SHA-256 "
               + hashlib.sha256(aggregate).hexdigest().encode() + b"\n")
        for name, content in {
            "current-aggregate.json": aggregate,
            "current-disagreements.tsv": b"ontology\n",
            "current-results.tex": tex,
            "result-records.sha256": records,
            "SHA256SUMS": b"placeholder\n",
        }.items():
            (self.final / name).write_bytes(content)
        generated = self.root / "generated"
        generated.mkdir()
        (generated / "current-results.tex").write_bytes(tex)
        receipt = {
            "status": "verified",
            "result_records": 1512,
            "ontologies": 189,
            "baselines": [str(index) for index in range(8)],
            "aggregate_sha256": hashlib.sha256(aggregate).hexdigest(),
            "result_record_manifest_sha256": hashlib.sha256(records).hexdigest(),
        }
        (self.final / "import-verification.json").write_text(json.dumps(receipt))
        (self.final / "evidence-archive-verification.json").write_text(json.dumps({
            "status": "verified",
            "result_records": 1512,
            "final_aggregate_sha256": hashlib.sha256(aggregate).hexdigest(),
            "archive_sha256": "a" * 64,
        }))

    def tearDown(self):
        MODULE.ROOT = self.old_root
        self.temporary.cleanup()

    def test_verified_digest_bound_import_is_ready(self):
        self.assertTrue(MODULE.current_obo_ready())

    def test_changed_generated_table_binding_fails_closed(self):
        (self.root / "generated" / "current-results.tex").write_text("changed\n")
        self.assertFalse(MODULE.current_obo_ready())

    def test_changed_aggregate_fails_closed(self):
        (self.final / "current-aggregate.json").write_text('{"schema":2}\n')
        self.assertFalse(MODULE.current_obo_ready())

    def test_archive_bound_to_another_aggregate_fails_closed(self):
        path = self.final / "evidence-archive-verification.json"
        payload = json.loads(path.read_text())
        payload["final_aggregate_sha256"] = "b" * 64
        path.write_text(json.dumps(payload))
        self.assertFalse(MODULE.current_obo_ready())


if __name__ == "__main__":
    unittest.main()
