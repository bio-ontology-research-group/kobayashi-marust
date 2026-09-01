from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from import_fable_reviews import ASPECTS, import_reviews, verify


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(root: Path) -> tuple[Path, Path]:
    manuscript = root / "main.tex"
    manuscript.write_text("manuscript\n", encoding="utf-8")
    manuscript_hash = digest(manuscript)
    source = root / "source"
    source.mkdir()
    rows = []
    for number, (title, _) in ASPECTS.items():
        stem = f"{number:02d}-review"
        report = source / f"{stem}.md"
        report.write_text(
            f"# Review {number}: {title}\n\n{manuscript_hash}\n\n"
            "## Major findings\nNone\n\n## Minor findings\nNone\n\n## Verdict\nOK\n",
            encoding="utf-8")
        raw = source / f"{stem}.json"
        raw.write_text(json.dumps({"result": report.read_text(), "usage": {
            "output_tokens": 10}}), encoding="utf-8")
        rows.append({"review": str(number), "aspect": title, "model": "fable",
                     "manuscript_sha256": manuscript_hash, "seconds": "1.0",
                     "input_tokens": "1", "output_tokens": "10",
                     "cache_creation_tokens": "0", "cache_read_tokens": "0",
                     "raw_sha256": digest(raw), "report_sha256": digest(report),
                     "status": "complete"})
    fields = tuple(rows[0])
    with (source / "manifest.tsv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, delimiter="\t")
        writer.writeheader(); writer.writerows(rows)
    return source, manuscript


class ImportFableReviewsTest(unittest.TestCase):
    def test_seven_reviews_verify_and_import(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source, manuscript = fixture(root)
            self.assertEqual(len(verify(source, manuscript)), 7)
            target = root / "reviews"
            import_reviews(source, manuscript, target)
            self.assertTrue((target / "citations.md").is_file())
            self.assertFalse((target / "dispositions.tsv").exists())

    def test_changed_manuscript_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source, manuscript = fixture(Path(directory))
            manuscript.write_text("changed\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "another manuscript"):
                verify(source, manuscript)


if __name__ == "__main__":
    unittest.main()
