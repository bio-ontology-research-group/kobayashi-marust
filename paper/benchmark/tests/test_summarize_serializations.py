#!/usr/bin/env python3

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from summarize_serializations import receipt


class SerializationSummaryTest(unittest.TestCase):
    def test_import_provenance_rows_are_accepted_but_malformed_rows_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "receipt.tsv"
            path.write_text(
                "M\tmerged_sha256\t" + "a" * 64 + "\n"
                "I\tOntologyID(<x>)\tfile:/x.owl\t17\n"
                "Z\tcomplete\n", encoding="utf-8")
            self.assertEqual(receipt(path)["merged_sha256"], "a" * 64)
            path.write_text("I\tmissing\tfield\nZ\tcomplete\n", encoding="utf-8")
            with self.assertRaises(ValueError):
                receipt(path)


if __name__ == "__main__":
    unittest.main()
