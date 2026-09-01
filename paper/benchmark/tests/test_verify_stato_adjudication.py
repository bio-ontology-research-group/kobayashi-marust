from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path
import sys


BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
from verify_stato_adjudication import verify  # noqa: E402


class StatoAdjudicationTest(unittest.TestCase):
    def test_archived_adjudication_is_bound_and_replays(self) -> None:
        root = BENCHMARK / "generated" / "disagreement-evidence" / "stato"
        report = verify(root)
        self.assertEqual(report["status"], "jfact-only-bottom-reproduced")
        self.assertFalse(report["hermit_bottom_entailed"])

    def test_changed_result_fails_closed(self) -> None:
        source = (BENCHMARK / "generated" / "disagreement-evidence" / "stato" /
                  "results" / "openllet" / "stato-0000073-module.result.json")
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "stato"
            shutil.copytree(source.parents[2], root)
            target = root / "results" / "openllet"
            data = json.loads(source.read_text(encoding="utf-8"))
            data["unsatisfiable"] = 1
            (target / source.name).write_text(json.dumps(data), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "digest mismatch"):
                verify(root)


if __name__ == "__main__":
    unittest.main()
