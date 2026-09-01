import hashlib
import json
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence" / "laptop"


class LaptopEvidenceTest(unittest.TestCase):
    def test_import_manifest_and_attribution_boundaries(self):
        for line in (EVIDENCE / "SHA256SUMS").read_text().splitlines():
            expected, name = line.split(None, 1)
            actual = hashlib.sha256((EVIDENCE / name.strip()).read_bytes()).hexdigest()
            self.assertEqual(expected, actual, name)
        report = json.loads((EVIDENCE / "import-report.json").read_text())
        km = report["projects"]["kobayashi_marust"]
        self.assertEqual(681, km["sessions"])
        self.assertEqual(21, km["top_level"])
        self.assertEqual(660, km["children"])
        self.assertIn("upper bound", report["attribution_policy"]["neuro_symbolic_independence"])
        self.assertEqual("excluded housekeeping session",
                         report["attribution_policy"]["neuro_symbolic"])

    def test_session_exports_are_scrubbed(self):
        for path in EVIDENCE.glob("sessions-*.json"):
            data = json.loads(path.read_text())
            self.assertIn("first_message", data["fields_removed"])
            for row in data["sessions"]:
                self.assertNotIn("first_message", row)
                self.assertEqual("laptop", row.get("machine", "laptop"))


if __name__ == "__main__":
    unittest.main()
