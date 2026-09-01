from __future__ import annotations

import csv
import hashlib
from pathlib import Path
import tempfile
import unittest

from verify_review_dispositions import REPORTS, verify


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(root: Path, with_finding: bool) -> tuple[Path, Path, Path]:
    manuscript = root / "main.tex"
    manuscript.write_text("revised manuscript\n", encoding="utf-8")
    reviews = root / "reviews"
    reviews.mkdir()
    reviewed_hash = "a" * 64
    usage = []
    for number, name in REPORTS.items():
        major = "1. Important issue\n" if with_finding and number == 1 else "None\n"
        report = reviews / name
        report.write_text(
            f"# Review {number}\n{reviewed_hash}\n## Major findings\n{major}"
            "## Minor findings\nNone\n## Verdict\nOK\n", encoding="utf-8")
        usage.append({"review": number, "manuscript_sha256": reviewed_hash,
                      "report_sha256": digest(report)})
    with (reviews / "review-usage.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream,
                                fieldnames=("review", "manuscript_sha256", "report_sha256"),
                                delimiter="\t")
        writer.writeheader(); writer.writerows(usage)
    dispositions = reviews / "dispositions.tsv"
    dispositions.write_text(
        "review\tseverity\tfinding\tdisposition\trationale\tmanuscript_action\n",
        encoding="utf-8")
    return reviews, manuscript, dispositions


class VerifyReviewDispositionsTest(unittest.TestCase):
    def test_explicit_none_reports_need_no_rows(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            reviews, manuscript, dispositions = fixture(Path(directory), False)
            report = verify(reviews, manuscript, dispositions)
            self.assertEqual(report["findings"], 0)

    def test_undisposed_finding_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            reviews, manuscript, dispositions = fixture(Path(directory), True)
            with self.assertRaisesRegex(ValueError, "undisposed"):
                verify(reviews, manuscript, dispositions)


if __name__ == "__main__":
    unittest.main()
