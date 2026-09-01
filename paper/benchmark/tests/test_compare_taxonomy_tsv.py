import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from compare_taxonomy_tsv import compare, pairs


class CompareTaxonomyTsvTest(unittest.TestCase):
    def test_streaming_difference(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            left = root / "left.tsv"
            right = root / "right.tsv"
            left.write_text("M\tschema\t1\nS\tA\tB\nS\tA\tC\nS\tD\tE\n")
            right.write_text("C\ttrue\nS\tA\tB\nS\tA\tD\nS\tD\tE\n")
            result = compare(left, right, 5)
            self.assertEqual(result["common"], 2)
            self.assertEqual(result["left_only"], 1)
            self.assertEqual(result["right_only"], 1)
            self.assertEqual(result["relation"], "incomparable")
            self.assertEqual(result["left_only_sample"], [["A", "C"]])

    def test_duplicate_fails(self):
        source = Path("duplicate.tsv")
        with self.assertRaisesRegex(ValueError, "duplicate"):
            list(pairs(io.StringIO("S\tA\tB\nS\tA\tB\n"), source))

    def test_unsorted_fails(self):
        source = Path("unsorted.tsv")
        with self.assertRaisesRegex(ValueError, "unsorted"):
            list(pairs(io.StringIO("S\tB\tC\nS\tA\tC\n"), source))


if __name__ == "__main__":
    unittest.main()
