from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from run_fable_reviews import briefs, extract_report


PAPER = Path(__file__).resolve().parents[1]


class RunFableReviewsTest(unittest.TestCase):
    def test_seven_nonoverlapping_briefs_parse(self) -> None:
        parsed = briefs(PAPER / "review-prompts.md")
        self.assertEqual(set(parsed), set(range(1, 8)))
        self.assertEqual(parsed[1][0], "Overall structure")

    def test_report_requires_hash_headings_and_usage(self) -> None:
        manuscript_hash = hashlib.sha256((PAPER / "main.tex").read_bytes()).hexdigest()
        result = ("# Review 1: Overall structure\n\n" + manuscript_hash +
                  "\n\n## Major findings\nNone\n\n## Minor findings\nNone\n\n"
                  "## Verdict\nAcceptable\n")
        payload = {"result": result, "usage": {"input_tokens": 10,
                   "output_tokens": 20, "cache_creation_input_tokens": 30,
                   "cache_read_input_tokens": 40}}
        with tempfile.TemporaryDirectory() as directory:
            raw = Path(directory) / "raw.json"
            report = Path(directory) / "report.md"
            raw.write_text(json.dumps(payload), encoding="utf-8")
            usage = extract_report(raw, report, 1, "Overall structure", manuscript_hash)
            self.assertEqual(usage["output_tokens"], 20)
            self.assertTrue(report.is_file())


if __name__ == "__main__":
    unittest.main()
