#!/usr/bin/env python3
"""Regression tests for profile-aware current-corpus aggregation."""

from __future__ import annotations

import csv
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


BASELINES = ("km", "konclude", "hermit", "jfact", "openllet", "more", "elk", "whelk")
EXPRESSIVE = ("km", "konclude", "hermit", "jfact", "openllet", "more")
SCRIPT = Path(__file__).resolve().parents[1] / "aggregate_current.py"
RENDER = Path(__file__).resolve().parents[1] / "render_current_tables.py"


class AggregateCurrentTest(unittest.TestCase):
    def test_more_participates_in_relation_but_not_consistency_consensus(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            manifest = root / "manifest.tsv"
            baselines = root / "baselines.tsv"
            execution_jobs = root / "execution-jobs.tsv"
            preparation_artifacts = root / "preparation-artifacts.tsv"
            receipts = root / "receipts"
            serialization_receipts = root / "serialization-receipts"
            profiles = root / "profiles"
            results = root / "results"
            receipts.mkdir(); serialization_receipts.mkdir(); profiles.mkdir(); results.mkdir()

            with manifest.open("w", newline="", encoding="utf-8") as stream:
                writer = csv.DictWriter(stream, fieldnames=("id", "eligible"), delimiter="\t")
                writer.writeheader()
                identifiers = ["ncit", "uberon", "chebi"] + [f"o{i:03d}" for i in range(186)]
                writer.writerows({"id": identifier, "eligible": "true"} for identifier in identifiers)
            with baselines.open("w", newline="", encoding="utf-8") as stream:
                writer = csv.DictWriter(stream, fieldnames=("id", "version_or_commit", "artifact_sha256"), delimiter="\t")
                writer.writeheader()
                writer.writerows({"id": baseline, "version_or_commit": f"{baseline}-test",
                                  "artifact_sha256": baseline[0] * 64}
                                 for baseline in BASELINES)
            with execution_jobs.open("w", newline="", encoding="utf-8") as stream:
                writer = csv.DictWriter(
                    stream, fieldnames=("id", "runner_sha256", "allowed_array_job_ids"),
                    delimiter="\t")
                writer.writeheader()
                writer.writerows({"id": baseline, "runner_sha256": "d" * 64,
                                  "allowed_array_job_ids": "12345"}
                                 for baseline in BASELINES)
            converter_digest = "f" * 64
            with preparation_artifacts.open("w", newline="", encoding="utf-8") as stream:
                writer = csv.DictWriter(stream, fieldnames=("id", "runtime_sha256"), delimiter="\t")
                writer.writeheader()
                writer.writerow({"id": "verified-xml-converter", "runtime_sha256": converter_digest})

            relation_a = "a" * 64
            relation_b = "b" * 64
            for index, ontology in enumerate(identifiers):
                input_digest = f"{index:064x}"
                (receipts / f"{ontology}.tsv").write_text(
                    f"M\tmerged_sha256\t{input_digest}\nZ\tcomplete\n", encoding="utf-8")
                serialized_digest = f"{index + 1000:064x}"
                (serialization_receipts / f"{ontology}.tsv").write_text(
                    "M\tconversion\tkonclude-compatible-serialization-v2\n"
                    f"M\tconverter_sha256\t{converter_digest}\n"
                    f"M\tsource_sha256\t{input_digest}\n"
                    f"M\toutput_sha256\t{serialized_digest}\n"
                    "M\troundtrip_logical_axioms_equal\ttrue\n"
                    "M\troundtrip_signature_equal\ttrue\nZ\tcomplete\n", encoding="utf-8")
                (profiles / f"{ontology}.tsv").write_text(
                    f"M\tlogical_axioms\t{index * 1000}\n"
                    + "".join(f"P\t{name}\ttrue\t0\n"
                            for name in ("OWL2", "OWL2DL", "OWL2EL", "OWL2QL", "OWL2RL"))
                    + "Z\tcomplete\n", encoding="utf-8")
                for baseline in BASELINES:
                    directory = results / baseline
                    directory.mkdir(exist_ok=True)
                    relation = relation_b if ontology == "ncit" and baseline == "more" else relation_a
                    record = {
                        "schema": 1, "baseline": baseline, "ontology_id": ontology,
                        "ontology_sha256": input_digest, "status": "ok", "checkpointed": True,
                        "peak_mb": 1.0, "wall_s": 1.0, "taxonomy_sha256": "c" * 64,
                        "relation_sha256": relation,
                        "consistency": "unknown" if baseline == "more" else "true",
                        "runner_sha256": "d" * 64,
                        "slurm_array_job_id": "12345",
                    }
                    if baseline == "km": record["input_ontology_sha256"] = input_digest
                    if baseline == "konclude": record["input_ontology_sha256"] = serialized_digest
                    record["binary_sha256" if baseline in {"km", "konclude"} else "runtime_sha256"] = baseline[0] * 64
                    (directory / f"{ontology}.result.json").write_text(
                        json.dumps(record), encoding="utf-8")

            output = root / "aggregate.json"
            disagreements = root / "disagreements.tsv"
            subprocess.run([
                sys.executable, str(SCRIPT), "--manifest", str(manifest),
                "--baselines", str(baselines), "--receipts", str(receipts),
                "--execution-jobs", str(execution_jobs),
                "--preparation-artifacts", str(preparation_artifacts),
                "--serialization-receipts", str(serialization_receipts),
                "--profiles", str(profiles), "--results", str(results),
                "--output-json", str(output), "--disagreements-tsv", str(disagreements),
            ], check=True, capture_output=True, text=True)
            aggregate = json.loads(output.read_text(encoding="utf-8"))

            self.assertEqual(aggregate["status_counts_owl2dl"],
                             {baseline: {"ok": 189} for baseline in BASELINES})
            self.assertEqual(aggregate["execution_bindings"]["km"], {
                "runner_sha256": "d" * 64, "allowed_array_job_ids": ["12345"]})
            relation_counts = aggregate["expressive_relation_agreement_owl2dl_inputs"]
            self.assertEqual(relation_counts["all_expressive_complete_disagree"], 1)
            self.assertEqual(relation_counts["all_expressive_complete_agree"], 188)
            self.assertEqual(aggregate["consistency_agreement_owl2dl_inputs"],
                             {"all_capable_complete_agree": 189})
            self.assertEqual(
                aggregate["km_against_unanimous_external_consensus_owl2dl_inputs"],
                {"km_agrees_unanimous_external": 188, "external_disagreement": 1},
            )
            km_more = aggregate["pairwise_relation_agreement"]["km:more"]
            self.assertEqual(km_more["relation_agreements_owl2dl"], 188)
            self.assertEqual(km_more["performance_on_relation_agreements_owl2dl"]
                             ["left"]["wall_s"], {"n": 188, "mean": 1.0, "median": 1.0})
            self.assertEqual(km_more["performance_on_relation_agreements_owl2dl"]
                             ["right"]["peak_mb"], {"n": 188, "mean": 1.0, "median": 1.0})
            with disagreements.open(encoding="utf-8") as stream:
                row = list(csv.DictReader(stream, delimiter="\t"))[0]
            self.assertEqual(row["ontology"], "ncit")
            self.assertIn("more=" + relation_b, row["relation_groups"])
            self.assertNotIn("more=unknown", row["consistency_values"])
            self.assertEqual(set(EXPRESSIVE), {part.split("=")[0]
                                                for group in row["relation_groups"].split(";")
                                                for part in group.split("=")[0].split(",")})
            tables = root / "tables.tex"
            subprocess.run([sys.executable, str(RENDER), "--aggregate", str(output),
                            "--output", str(tables)], check=True, capture_output=True, text=True)
            rendered = tables.read_text(encoding="utf-8")
            self.assertIn("KM & km-test & 189 & 0 & 0 & 0 & 0 & 1.000 & 1.000 & 1.0 & 1.0", rendered)
            self.assertIn("MORe & 188 & 1.000 & 1.000", rendered)
            self.assertIn("Mean s KM & Mean s ext.", rendered)
            self.assertIn("NCIt & OWL 2, DL, EL, QL, RL & ok & ok", rendered)
            self.assertEqual(aggregate["named_obo_hard_cases"]["ncit"]
                             ["expressive_relation_groups"][1]["baselines"], ["more"])
            self.assertEqual(aggregate["stratified_results"]["size"]["<1k"]["km"]
                             ["status_counts"], {"ok": 1})
            self.assertIn("KM & 189/189 (1.00 s)", rendered)

            # Named terminal failures must remain visible rather than falling
            # between the generic Error column and the performance metrics.
            other_payload = json.loads(output.read_text(encoding="utf-8"))
            other_payload["status_counts_owl2dl"]["konclude"] = {
                "ok": 188, "output_error": 1,
            }
            other_aggregate = root / "other-status.json"
            other_aggregate.write_text(json.dumps(other_payload), encoding="utf-8")
            other_tables = root / "other-status.tex"
            subprocess.run([sys.executable, str(RENDER), "--aggregate", str(other_aggregate),
                            "--output", str(other_tables)], check=True,
                           capture_output=True, text=True)
            self.assertIn("Konclude & konclude-test & 188 & 0 & 0 & 0 & 1 &",
                          other_tables.read_text(encoding="utf-8"))

            # Machine status/version strings are data, not trusted TeX.
            escaped_payload = json.loads(output.read_text(encoding="utf-8"))
            escaped_payload["baseline_artifacts"]["km"]["version_or_commit"] = "v_test%1"
            escaped_payload["named_obo_hard_cases"]["ncit"]["statuses"]["km"] = "output_error"
            escaped_aggregate = root / "escaped.json"
            escaped_aggregate.write_text(json.dumps(escaped_payload), encoding="utf-8")
            escaped_tables = root / "escaped.tex"
            subprocess.run([sys.executable, str(RENDER), "--aggregate", str(escaped_aggregate),
                            "--output", str(escaped_tables)], check=True,
                           capture_output=True, text=True)
            escaped_text = escaped_tables.read_text(encoding="utf-8")
            self.assertIn(r"v\_test\%1", escaped_text)
            self.assertIn(r"output\_error", escaped_text)

            # Unanimous inconsistency is one semantic relation even when
            # reasoners serialize an empty taxonomy, bottom classes, or
            # arbitrary relation digests differently.
            inconsistent_ontology = "o184"
            for index, baseline in enumerate(BASELINES):
                path = results / baseline / f"{inconsistent_ontology}.result.json"
                record = json.loads(path.read_text(encoding="utf-8"))
                record["relation_sha256"] = f"{index + 10:064x}"
                record["consistency"] = "unknown" if baseline in {"more", "elk", "whelk"} else "false"
                path.write_text(json.dumps(record), encoding="utf-8")
            inconsistent_output = root / "inconsistent.json"
            inconsistent_disagreements = root / "inconsistent.tsv"
            subprocess.run([
                sys.executable, str(SCRIPT), "--manifest", str(manifest),
                "--baselines", str(baselines), "--receipts", str(receipts),
                "--execution-jobs", str(execution_jobs),
                "--preparation-artifacts", str(preparation_artifacts),
                "--serialization-receipts", str(serialization_receipts),
                "--profiles", str(profiles), "--results", str(results),
                "--output-json", str(inconsistent_output),
                "--disagreements-tsv", str(inconsistent_disagreements),
            ], check=True, capture_output=True, text=True)
            normalized = json.loads(inconsistent_output.read_text(encoding="utf-8"))
            self.assertEqual(normalized["unanimously_inconsistent_relation_normalization"],
                             [inconsistent_ontology])
            self.assertEqual(normalized["expressive_relation_agreement_owl2dl_inputs"]
                             ["all_expressive_complete_disagree"], 1)
            self.assertEqual(normalized["pairwise_relation_agreement"]["km:more"]
                             ["relation_disagreements_owl2dl"], 1)
            with inconsistent_disagreements.open(encoding="utf-8") as stream:
                self.assertEqual([row["ontology"] for row in
                                  csv.DictReader(stream, delimiter="\t")], ["ncit"])

            stale_path = results / "jfact" / "o185.result.json"
            stale_record = json.loads(stale_path.read_text(encoding="utf-8"))
            stale_record["slurm_array_job_id"] = "unrelated-job"
            stale_path.write_text(json.dumps(stale_record), encoding="utf-8")
            stale = subprocess.run([
                sys.executable, str(SCRIPT), "--manifest", str(manifest),
                "--baselines", str(baselines), "--execution-jobs", str(execution_jobs),
                "--receipts", str(receipts),
                "--preparation-artifacts", str(preparation_artifacts),
                "--serialization-receipts", str(serialization_receipts),
                "--profiles", str(profiles), "--results", str(results),
                "--output-json", str(root / "stale.json"),
                "--disagreements-tsv", str(root / "stale.tsv"),
            ], capture_output=True, text=True)
            self.assertNotEqual(stale.returncode, 0)
            self.assertIn("refusing incomplete aggregate", stale.stderr)
            self.assertFalse((root / "stale.json").exists())
            stale_record["slurm_array_job_id"] = "12345"
            stale_path.write_text(json.dumps(stale_record), encoding="utf-8")

            (results / "more" / "o185.result.json").unlink()
            incomplete = subprocess.run([
                sys.executable, str(SCRIPT), "--manifest", str(manifest),
                "--baselines", str(baselines), "--receipts", str(receipts),
                "--execution-jobs", str(execution_jobs),
                "--preparation-artifacts", str(preparation_artifacts),
                "--serialization-receipts", str(serialization_receipts),
                "--profiles", str(profiles), "--results", str(results),
                "--output-json", str(root / "incomplete.json"),
                "--disagreements-tsv", str(root / "incomplete.tsv"),
            ], capture_output=True, text=True)
            self.assertNotEqual(incomplete.returncode, 0)
            self.assertIn("refusing incomplete aggregate", incomplete.stderr)
            self.assertFalse((root / "incomplete.json").exists())


if __name__ == "__main__":
    unittest.main()
