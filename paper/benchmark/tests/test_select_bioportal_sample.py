#!/usr/bin/env python3
"""Tests for outcome-independent BioPortal panel selection."""

from __future__ import annotations

import csv
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).parents[1] / "select_bioportal_sample.py"


class SelectBioPortalSampleTest(unittest.TestCase):
    def test_selection_is_quota_bounded_and_input_order_independent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            profiles = root / "profiles"; profiles.mkdir()
            candidates = []
            for index in range(12):
                acronym = f"O{index:02d}"
                candidates.append({"acronym": acronym, "submission_id": str(index),
                                   "source_sha256": f"{index:064x}", "eligible": "true",
                                   "exclusion_reason": ""})
                (profiles / f"{acronym}.tsv").write_text(
                    "M\tlogical_axioms\t500\nP\tOWL2DL\ttrue\t0\nP\tOWL2EL\ttrue\t0\nZ\tcomplete\n",
                    encoding="utf-8",
                )
            candidates.append({"acronym": "PRIVATE", "submission_id": "1",
                               "source_sha256": "f" * 64, "eligible": "false",
                               "exclusion_reason": "restricted"})

            selections = []
            for iteration, ordered in enumerate((candidates, list(reversed(candidates)))):
                manifest = root / f"candidates-{iteration}.tsv"
                with manifest.open("w", encoding="utf-8", newline="") as stream:
                    writer = csv.DictWriter(stream, fieldnames=ordered[0].keys(), delimiter="\t")
                    writer.writeheader(); writer.writerows(ordered)
                output = root / f"selection-{iteration}.tsv"
                subprocess.run([sys.executable, str(SCRIPT), "--candidates", str(manifest),
                                "--profiles", str(profiles), "--output", str(output)],
                               check=True, capture_output=True, text=True)
                with output.open(encoding="utf-8", newline="") as stream:
                    rows = list(csv.DictReader(stream, delimiter="\t"))
                selections.append({row["acronym"] for row in rows if row["selected"] == "true"})
                private = next(row for row in rows if row["acronym"] == "PRIVATE")
                self.assertEqual(private["selection_reason"], "restricted")
            self.assertEqual(selections[0], selections[1])
            self.assertEqual(len(selections[0]), 10)


if __name__ == "__main__":
    unittest.main()
