from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import sys


BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
from import_current_final import BASELINES, import_final, verify  # noqa: E402


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fixture(root: Path) -> Path:
    source = root / "source"
    source.mkdir()
    counts = {baseline: {"ok": 189} for baseline in BASELINES}
    aggregate = {
        "schema": 1, "eligible_ontologies": 189, "expected_runs": 1512,
        "missing_or_invalid_records": 0, "invalid_records": [],
        "status_counts": counts,
        "baseline_artifacts": {baseline: {} for baseline in BASELINES},
        "execution_bindings": {baseline: {} for baseline in BASELINES},
    }
    aggregate_path = source / "current-aggregate.json"
    aggregate_path.write_text(json.dumps(aggregate, sort_keys=True) + "\n", encoding="utf-8")
    aggregate_digest = sha(aggregate_path)
    (source / "current-results.tex").write_text(
        f"% Generated from aggregate SHA-256 {aggregate_digest}\nTABLE\n", encoding="utf-8")
    (source / "current-disagreements.tsv").write_text(
        "ontology\towl2dl\trelation_category\trelation_groups\tconsistency_category\tconsistency_values\n",
        encoding="utf-8")
    records = []
    for baseline in BASELINES:
        for index in range(189):
            name = f"current-results/{baseline}/o{index:03d}.result.json"
            records.append(f"{index:064x}  {name}\n")
    (source / "result-records.sha256").write_text("".join(records), encoding="utf-8")
    (source / "SHA256SUMS").write_text("".join(
        f"{sha(source / name)}  {name}\n" for name in (
            "current-aggregate.json", "current-disagreements.tsv",
            "current-results.tex", "result-records.sha256")), encoding="utf-8")
    return source


class ImportCurrentFinalTest(unittest.TestCase):
    def test_complete_matrix_verifies_and_imports_atomically(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = fixture(root)
            report = verify(source)
            self.assertEqual(report["result_records"], 1512)
            target = root / "target"
            tex = root / "paper" / "current-results.tex"
            imported = import_final(source, target, tex)
            self.assertEqual(imported, report)
            self.assertEqual(tex.read_bytes(), (source / "current-results.tex").read_bytes())
            self.assertTrue((target / "import-verification.json").is_file())

    def test_duplicate_record_index_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = fixture(Path(directory))
            manifest = source / "result-records.sha256"
            rows = manifest.read_text(encoding="utf-8").splitlines()
            rows[-1] = rows[-2]
            manifest.write_text("\n".join(rows) + "\n", encoding="utf-8")
            sums = source / "SHA256SUMS"
            sums.write_text(sums.read_text(encoding="utf-8").replace(
                next(line for line in sums.read_text().splitlines()
                     if line.endswith("result-records.sha256")).split()[0], sha(manifest)),
                encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate digest-manifest path"):
                verify(source)

    def test_verified_import_can_replace_existing_atomically(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = fixture(root)
            target = root / "target"
            tex = root / "paper" / "current-results.tex"
            import_final(source, target, tex)
            (target / "stale-marker").write_text("old\n")
            import_final(source, target, tex, replace_existing=True)
            self.assertFalse((target / "stale-marker").exists())
            self.assertFalse(target.with_name("target.previous").exists())
            self.assertTrue((target / "import-verification.json").is_file())


if __name__ == "__main__":
    unittest.main()
