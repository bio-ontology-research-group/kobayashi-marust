from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
import sys


BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
from verify_uo_nominal_witness import verify  # noqa: E402


class UoNominalWitnessTest(unittest.TestCase):
    def test_archived_witness_replays(self) -> None:
        witness = (BENCHMARK / "generated" / "disagreement-evidence" /
                   "uo" / "witness.tsv")
        report = verify(witness)
        self.assertEqual(report["status"], "entailed")
        self.assertEqual(report["premise_count"], 3)

    def test_non_punning_singleton_fails(self) -> None:
        witness = (BENCHMARK / "generated" / "disagreement-evidence" /
                   "uo" / "witness.tsv")
        altered = witness.read_text(encoding="utf-8").replace(
            "ObjectOneOf(<http://purl.obolibrary.org/obo/UO_0000244>)",
            "ObjectOneOf(<urn:not-the-punned-individual>)", 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "witness.tsv"
            path.write_text(altered, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "punning"):
                verify(path)


if __name__ == "__main__":
    unittest.main()
