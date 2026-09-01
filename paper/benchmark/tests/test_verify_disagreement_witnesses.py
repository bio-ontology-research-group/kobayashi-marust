from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

import sys


BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
from verify_disagreement_witnesses import verify_cvdo, verify_doid, verify_kisao  # noqa: E402


class DisagreementWitnessTest(unittest.TestCase):
    def test_archived_witnesses_replay(self) -> None:
        root = BENCHMARK / "generated" / "disagreement-evidence"
        self.assertEqual(verify_doid(root / "doid" / "explanation.tsv")["status"], "entailed")
        self.assertEqual(verify_cvdo(root / "cvdo" / "explanation.tsv")["status"], "entailed")
        self.assertEqual(verify_kisao(root / "kisao" / "explanation.tsv")["status"], "entailed")

    def test_missing_premise_fails_closed(self) -> None:
        source = (BENCHMARK / "generated" / "disagreement-evidence" /
                  "cvdo" / "explanation.tsv").read_text(encoding="utf-8")
        altered = "\n".join(line for line in source.splitlines()
                            if "CVDO_0000010" not in line) + "\n"
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "altered.tsv"
            path.write_text(altered, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "missing witness premises"):
                verify_cvdo(path)


if __name__ == "__main__":
    unittest.main()
