#!/usr/bin/env python3
"""Reasoner-free tests for the fail-closed route evidence helpers."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from validate_documented_route import (
    read_row,
    run_checks,
    selected_route_from_stderr,
    selected_routes_from_stderr,
    semantic_checks,
    verify_konclude_build_receipt,
    verify_sha256_manifest,
)
from generate_reproduced_route_ledger import (
    canonical_json_sha256,
    exact_candidate_is_success,
    ledger_route_observation,
    result_record_manifest_sha256,
    selected_structural_provenance_failures,
    selected_reference_is_current,
    terminal_route_attempt_detail,
)
from audit_10621_exact_tinput import source_abox


def digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


class RouteEvidenceTests(unittest.TestCase):
    def test_ledger_route_identity_requires_one_matching_trace(self) -> None:
        record = {
            "route": "cb_plain16",
            "selected_route_trace": "cb_plain16",
            "selected_route_trace_count": 1,
        }
        self.assertEqual(
            ledger_route_observation(record, "current_alternative_route"),
            ("runtime-trace", "runtime_trace", "cb_plain16"),
        )

        record["selected_route_trace_count"] = 2
        self.assertEqual(
            ledger_route_observation(record, "current_alternative_route"),
            ("", "", ""),
        )

        selected = {
            "effective_route_request": "ht_bridge",
            "selected_route_trace": "manual",
            "selected_route_trace_count": 1,
        }
        self.assertEqual(
            ledger_route_observation(selected, "current_selected_route"),
            ("", "", ""),
        )

    def test_source_built_konclude_receipt_binds_both_builds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "Konclude-build-a"
            binary.write_bytes(b"same-source-built-binary\n")
            binary_sha = digest(binary.read_bytes())
            driver = root / "build_reproducible_konclude_on_ws.sh"
            driver.write_bytes(b"#!/bin/bash\n")
            driver_sha = digest(driver.read_bytes())
            source_manifest_sha = "3" * 64
            runtime_manifest_sha = "4" * 64
            runtime_dir = root / "runtime-lib"
            runtime_dir.mkdir()
            receipt = {
                "schema_version": 2,
                "status": "verified_reproducible",
                "source": {
                    "repository": "https://github.com/konclude/Konclude.git",
                    "commit": "0002e80635403960a7df5d93bd0e8f994d4952d0",
                    "tag": "v0.7.0-1138",
                    "archive_sha256": "936b65796da3209eed83d90264614067bd7d8f03133d089a64dd8bea9618076f",
                    "source_date_epoch": 1624053538,
                    "manifest_sha256": source_manifest_sha,
                    "manifest_file_count": 5525,
                },
                "build": {
                    "project": "KoncludeWithoutRedland.pro",
                    "module": "qt/5.15.5/gnu-12.2.0",
                    "qmake_command": [
                        "qmake",
                        "-o",
                        "Makefile",
                        "KoncludeWithoutRedland.pro",
                        "CONFIG+=no_qt_rpath",
                        "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=SOURCE_TREE=.",
                        "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=SOURCE_TREE=.",
                        "QMAKE_LFLAGS+=-Wl,--build-id=sha1",
                    ],
                    "sequential_fresh_trees": True,
                    "jobs": 4,
                    "network_used": False,
                    "ld_run_path_cleared": True,
                    "slurm_job_id": 123,
                },
                "outputs": {
                    "byte_identical": True,
                    "build_a": "Konclude-build-a",
                    "build_b": "Konclude-build-b",
                    "build_a_sha256": binary_sha,
                    "build_b_sha256": binary_sha,
                },
                "runtime": {
                    "library_directory": str(runtime_dir),
                    "manifest_sha256": runtime_manifest_sha,
                    "manifest_file_count": 7,
                },
                "driver_sha256": driver_sha,
                "artifacts": {
                    "build_reproducible_konclude_on_ws.sh": driver_sha,
                    "Konclude-build-a": binary_sha,
                    "Konclude-build-b": binary_sha,
                    "source-files.sha256": source_manifest_sha,
                    "runtime-files.sha256": runtime_manifest_sha,
                },
            }
            receipt_path = root / "build-receipt.json"
            receipt_path.write_text(
                json.dumps(receipt, sort_keys=True) + "\n", encoding="utf-8"
            )
            loaded, checks = verify_konclude_build_receipt(
                receipt_path=receipt_path,
                expected_receipt_sha256=digest(receipt_path.read_bytes()),
                driver=driver,
                expected_driver_sha256=driver_sha,
                binary=binary,
                expected_binary_sha256=binary_sha,
                expected_source_manifest_sha256=source_manifest_sha,
                library_dir=runtime_dir,
                expected_runtime_manifest_sha256=runtime_manifest_sha,
                expected_runtime_count=7,
            )
            self.assertEqual(loaded, receipt)
            self.assertTrue(all(checks.values()), checks)

    def test_route_trace_requires_exactly_one_selection(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            stderr = Path(directory) / "stderr.log"
            stderr.write_text(
                "KM_TIMING frontend done elapsed=1 route=ht_bridge\n",
                encoding="utf-8",
            )
            self.assertEqual(selected_routes_from_stderr(stderr), ["ht_bridge"])
            self.assertEqual(selected_route_from_stderr(stderr), "ht_bridge")

            stderr.write_text(
                "KM_TIMING frontend done elapsed=1 route=ht_bridge\n"
                "KM_TIMING frontend done elapsed=2 route=manual\n",
                encoding="utf-8",
            )
            self.assertEqual(
                selected_routes_from_stderr(stderr), ["ht_bridge", "manual"]
            )
            self.assertEqual(selected_route_from_stderr(stderr), "")

    def test_alternative_validator_imports_under_isolated_python(self) -> None:
        script = Path(__file__).with_name("validate_alternative_route.py")
        completed = subprocess.run(
            ["/usr/bin/python3", "-I", str(script), "--help"],
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_10621_source_abox_expands_nary_different_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            ontology = Path(directory) / "small.owl"
            ontology.write_text(
                "Ontology(\n"
                "ClassAssertion(owl:Thing <a>)\n"
                "ClassAssertion(owl:Thing <b>)\n"
                "ClassAssertion(owl:Thing <c>)\n"
                "DifferentIndividuals(<a> <b> <c>)\n"
                ")\n",
                encoding="utf-8",
            )
            asserted, pairs, counts = source_abox(ontology)
            self.assertEqual(asserted, ["a", "b", "c"])
            self.assertEqual(pairs, [("a", "b"), ("a", "c"), ("b", "c")])
            self.assertEqual(counts["ClassAssertion"], 3)
            self.assertEqual(counts["DifferentIndividuals"], 1)

    def test_registry_row_count_is_explicit_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            registry = Path(directory) / "target.tsv"
            registry.write_text(
                "ontology\tstate\nore_ont_10621.owl\texact_gold\n",
                encoding="utf-8",
            )
            row, count = read_row(registry, 0, expected_count=1)
            self.assertEqual(row["ontology"], "ore_ont_10621.owl")
            self.assertEqual(count, 1)
            with self.assertRaisesRegex(ValueError, "must contain 592 rows"):
                read_row(registry, 0)

    def test_manifest_verifies_order_identity_and_file_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "A"
            second = root / "b"
            first.write_bytes(b"first\n")
            second.write_bytes(b"second\n")
            manifest = root / "files.sha256"
            payload = (
                f"{digest(first.read_bytes())}  {first}\n"
                f"{digest(second.read_bytes())}  {second}\n"
            ).encode("utf-8")
            manifest.write_bytes(payload)

            entries, checks = verify_sha256_manifest(
                manifest,
                expected_sha256=digest(payload),
                expected_count=2,
            )
            self.assertEqual([str(first), str(second)], [e["path"] for e in entries])
            self.assertTrue(all(checks.values()), checks)

            second.write_bytes(b"changed\n")
            _, changed_checks = verify_sha256_manifest(
                manifest,
                expected_sha256=digest(payload),
                expected_count=2,
            )
            self.assertFalse(changed_checks["manifest_files_match"])

    def test_run_checks_requires_closed_launcher_and_exact_command(self) -> None:
        command = ["/capsule/km", "classify", "/corpus/o.owl"]
        run = {
            "status": "ok",
            "return_code": 0,
            "binary_sha256": "a" * 64,
            "wall_s": 1.0,
            "peak_mb": 10.0,
            "cpus": 16,
            "command": command,
            "launcher": {
                "status": "verified",
                "checks": {"python": True, "gnu_time": True, "inner": True},
                "environment": {
                    "PATH": "/usr/bin:/bin",
                    "LC_ALL": "C",
                    "PYTHONHASHSEED": "0",
                },
                "wrapper_sha256": "b" * 64,
                "working_directory": "/",
            },
        }
        checks = run_checks(
            run,
            "a" * 64,
            240,
            20480,
            "b" * 64,
            command,
        )
        self.assertTrue(all(checks.values()), checks)

        run["launcher"]["environment"]["KM_ROUTE"] = "auto"
        open_checks = run_checks(
            run,
            "a" * 64,
            240,
            20480,
            "b" * 64,
            command,
        )
        self.assertFalse(open_checks["closed_launcher_environment"])

    def test_inconsistent_serializations_compare_semantically(self) -> None:
        km = {
            "consistent": False,
            "taxonomy_sha256": "km-empty",
            "subsumptions": 0,
            "unsatisfiable": 0,
            "source_ontology_sha256": "c" * 64,
        }
        reference = {
            "consistent": False,
            "taxonomy_sha256": "oracle-bottom-equivalent",
            "subsumptions": 999,
            "unsatisfiable": 100,
            "source_ontology_sha256": "c" * 64,
        }
        self.assertTrue(all(semantic_checks(km, reference).values()))

    def test_selected_reference_requires_closed_reproducible_oracle(self) -> None:
        reference_specification = {
            "command": ["/oracle", "classification"],
            "binary_sha256": "1" * 64,
            "ontology_sha256": "9" * 64,
            "build_receipt_sha256": "7" * 64,
            "source_manifest_sha256": "8" * 64,
            "build_driver_sha256": "0" * 64,
        }
        record = {
            "validation_protocol": (
                "reproducible-current-selected-full-iri-v2"
            ),
            "documented_state": "exact_gold",
            "ontology_sha256": "9" * 64,
            "actual_binary_sha256": "a" * 64,
            "executed_source_manifest_sha256": "b" * 64,
            "executed_build_receipt_sha256": "c" * 64,
            "km_runtime": {
                "runtime_library_manifest_sha256": "4" * 64,
                "ldd_sha256": "5" * 64,
            },
            "km_runtime_checks": {"closure": True},
            "validator_sha256": "d" * 64,
            "validation_driver_sha256": "6" * 64,
            "validation_driver_check": True,
            "runner_sha256": "e" * 64,
            "fingerprint_tool_sha256": "f" * 64,
            "validator_environment_checks": {"closed": True},
            "reference_ready": True,
            "reference_binary_sha256": "1" * 64,
            "reference_build_receipt_sha256": "7" * 64,
            "reference_build_checks": {"source_built": True},
            "reference_runtime": {
                "runtime_library_manifest_sha256": "2" * 64,
                "ldd_sha256": "5" * 64,
            },
            "reference_route_specification": reference_specification,
            "reference_route_specification_sha256": canonical_json_sha256(
                reference_specification
            ),
            "reference_runtime_checks": {"closure": True},
            "reference_checks": {"limits": True},
            "reference_fingerprint_checks": {"full_iri": True},
            "reference_fingerprint": {"taxonomy_sha256": "3" * 64},
        }
        arguments = {
            "binary": "a" * 64,
            "source": "b" * 64,
            "receipt": "c" * 64,
            "km_runtime": "4" * 64,
            "ldd": "5" * 64,
            "validator": "d" * 64,
            "validation_driver": "6" * 64,
            "runner": "e" * 64,
            "fingerprint": "f" * 64,
            "konclude": "1" * 64,
            "konclude_runtime": "2" * 64,
            "konclude_receipt": "7" * 64,
            "konclude_source": "8" * 64,
            "konclude_driver": "0" * 64,
        }
        self.assertTrue(selected_reference_is_current(record, **arguments))

        record["reference_runtime_checks"]["closure"] = False
        self.assertFalse(selected_reference_is_current(record, **arguments))

    def test_exact_candidate_requires_full_source_and_route_identity(self) -> None:
        hashes = {letter: letter * 64 for letter in "abcdefghijklmno"}
        commit = "1" * 40
        ontology_sha = hashes["o"]
        candidate = {
            "candidate": "a639ab5",
            "commit": commit,
            "binary_sha256": hashes["a"],
            "source_manifest_sha256": hashes["b"],
            "build_receipt_sha256": hashes["c"],
            "test_receipt_sha256": hashes["d"],
            "source_identity_sha256": hashes["e"],
            "runtime_manifest_sha256": hashes["f"],
        }
        registry = {
            "ontology": "ore_ont_541.owl",
            "ontology_sha256": ontology_sha,
            "route": "production_all",
            "route_environment": "KM_ROUTE=production_all",
            "source_revision": f"git:{commit}",
            "binary_sha256": hashes["a"],
            "rebuild_candidate": "a639ab5",
            "rebuild_source_commit": commit,
            "rebuild_source_manifest_sha256": hashes["b"],
            "rebuild_build_receipt_sha256": hashes["c"],
            "rebuild_test_receipt_sha256": hashes["d"],
            "rebuild_source_identity_sha256": hashes["e"],
            "rebuild_runtime_manifest_sha256": hashes["f"],
        }
        route_specification = {
            "semantic_environment": {"KM_ROUTE": "production_all"},
            "route_observation_policy": "runtime-trace",
        }
        reference_specification = {
            "binary_sha256": hashes["g"],
            "build_receipt_sha256": hashes["h"],
            "source_manifest_sha256": hashes["i"],
            "build_driver_sha256": hashes["j"],
            "ontology_sha256": ontology_sha,
        }
        record = {
            "confirmed": True,
            "confirmation_status": "confirmed_exact_full_iri",
            "validation_protocol": (
                "reproducible-exact-candidate-selected-full-iri-v1"
            ),
            "documented_state": "exact_gold",
            "documented_route": "production_all",
            "documented_source_revision": f"git:{commit}",
            "ontology": "ore_ont_541.owl",
            "ontology_sha256": ontology_sha,
            "actual_binary_sha256": hashes["a"],
            "executed_source_manifest_sha256": hashes["b"],
            "executed_build_receipt_sha256": hashes["c"],
            "km_runtime": {
                "runtime_library_manifest_sha256": hashes["f"],
                "ldd_sha256": hashes["k"],
            },
            "km_runtime_checks": {"closure": True},
            "validator_sha256": hashes["l"],
            "validation_driver_sha256": hashes["m"],
            "validation_driver_check": True,
            "runner_sha256": hashes["n"],
            "fingerprint_tool_sha256": hashes["o"],
            "validator_environment_checks": {"closed": True},
            "route_specification": route_specification,
            "route_specification_sha256": canonical_json_sha256(
                route_specification
            ),
            "semantic_environment_sha256": canonical_json_sha256(
                route_specification["semantic_environment"]
            ),
            "route_observation_policy": "runtime-trace",
            "route_observation_kind": "runtime_trace",
            "selected_route_trace_count": 1,
            "selected_route_trace": "production_all",
            "selected_route_traces": ["production_all"],
            "observed_route_identity": "production_all",
            "effective_route_request": "production_all",
            "current_route_label": "production_all",
            "parsed_environment": ["KM_ROUTE=production_all"],
            "checks": {"full_iri": True},
            "reference_ready": True,
            "reference_binary_sha256": hashes["g"],
            "reference_build_receipt_sha256": hashes["h"],
            "reference_build_checks": {"source_built": True},
            "reference_runtime": {
                "runtime_library_manifest_sha256": hashes["i"],
                "ldd_sha256": hashes["k"],
            },
            "reference_route_specification": reference_specification,
            "reference_route_specification_sha256": canonical_json_sha256(
                reference_specification
            ),
            "reference_runtime_checks": {"closure": True},
            "reference_checks": {"limits": True},
            "reference_fingerprint_checks": {"full_iri": True},
            "reference_fingerprint": {"taxonomy_sha256": hashes["a"]},
        }
        arguments = {
            "registry_row": registry,
            "candidate": candidate,
            "ldd": hashes["k"],
            "validator": hashes["l"],
            "validation_driver": hashes["m"],
            "runner": hashes["n"],
            "fingerprint": hashes["o"],
            "konclude": hashes["g"],
            "konclude_runtime": hashes["i"],
            "konclude_receipt": hashes["h"],
            "konclude_source": hashes["i"],
            "konclude_driver": hashes["j"],
        }
        self.assertTrue(exact_candidate_is_success(record, **arguments))
        registry["rebuild_test_receipt_sha256"] = "0" * 64
        self.assertFalse(exact_candidate_is_success(record, **arguments))

    def test_result_manifest_binds_order_name_and_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "results" / "first.json"
            second = root / "results" / "second.json"
            first.parent.mkdir()
            first.write_bytes(b"first\n")
            second.write_bytes(b"second\n")
            count, digest_in_order = result_record_manifest_sha256(
                [first, second], root=root
            )
            _, digest_reversed = result_record_manifest_sha256(
                [second, first], root=root
            )
            self.assertEqual(count, 2)
            self.assertNotEqual(digest_in_order, digest_reversed)

            second.write_bytes(b"changed\n")
            _, digest_changed = result_record_manifest_sha256(
                [first, second], root=root
            )
            self.assertNotEqual(digest_in_order, digest_changed)

    def test_selected_negative_result_is_not_relabelled_as_provenance(self) -> None:
        summary = {
            "failed_claims": ["negative.owl", "broken.owl"],
            "provenance_failures": {
                "negative.owl": ["all_acceptance_checks"],
                "broken.owl": ["validator"],
                "not-a-failed-claim.owl": ["all_acceptance_checks"],
            },
        }
        self.assertEqual(
            selected_structural_provenance_failures(summary),
            {"broken.owl", "not-a-failed-claim.owl"},
        )

    def test_terminal_route_failure_keeps_actionable_worker_reason(self) -> None:
        detail = terminal_route_attempt_detail(
            {
                "confirmation_status": "validation_error",
                "error": "outer wrapper noise",
                "km_run": {
                    "status": "error",
                    "return_code": 3,
                    "wall_s": 0.06,
                    "peak_mb": 12.0,
                    "stderr_tail": (
                        "route=ht_bridge\n"
                        "unsupported: selected HT mechanism deferred\n"
                    ),
                },
            }
        )
        self.assertEqual(detail["return_code"], 3)
        self.assertIn("unsupported", detail["stderr_tail"])
        self.assertNotIn("error_tail", detail)


if __name__ == "__main__":
    unittest.main()
