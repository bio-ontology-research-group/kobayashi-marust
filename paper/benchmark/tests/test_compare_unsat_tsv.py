import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from compare_unsat_tsv import compare, names


class CompareUnsatTsvTest(unittest.TestCase):
    def test_streaming_difference(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            left = root / "left.tsv"
            right = root / "right.tsv"
            left.write_text("M\tschema\t1\nU\tA\nU\tC\n")
            right.write_text("C\ttrue\nU\tA\nU\tB\n")
            result = compare(left, right, 5)
            self.assertEqual(result["common"], 1)
            self.assertEqual(result["left_only_sample"], ["C"])
            self.assertEqual(result["right_only_sample"], ["B"])
            self.assertEqual(result["relation"], "incomparable")

    def test_duplicate_fails(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            list(names(io.StringIO("U\tA\nU\tA\n"), Path("duplicate.tsv")))


if __name__ == "__main__":
    unittest.main()
