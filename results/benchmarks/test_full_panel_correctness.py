#!/usr/bin/env python3

from __future__ import annotations

import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from full_panel_correctness import classify_correctness


def reference(ontology: str, taxonomy: str = "reference") -> dict:
    return {
        "ont": ontology,
        "arm": "konclude",
        "status": "ok",
        "gold_kind": "konclude",
        "verdict": "match",
        "fulliri_fingerprint_status": "ok",
        "fulliri_taxonomy_sha256": taxonomy,
        "fulliri_identity_capable": True,
        "consistent": True,
    }


def answer(ontology: str, taxonomy: str = "answer") -> dict:
    return {
        "ont": ontology,
        "arm": "km_route_auto",
        "status": "ok",
        "gold_kind": "konclude",
        "verdict": "match",
        "fulliri_fingerprint_status": "ok",
        "fulliri_taxonomy_sha256": taxonomy,
        "fulliri_identity_capable": True,
        "consistent": True,
    }


class CorrectnessTests(unittest.TestCase):
    def test_shared_inconsistency_is_semantic_identity(self) -> None:
        ref = reference("ore_ont_443.owl", "materialized-bottom")
        ref.update(consistent=False, fulliri_unsatisfiable=39)
        row = answer("ore_ont_443.owl", "empty-inconsistent")
        row.update(consistent=False, fulliri_unsatisfiable=0)
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("yes", "yes"))
        self.assertEqual(row["correctness_basis"], "same_job_shared_inconsistency")

    def test_consistency_disagreement_is_not_hidden_by_reference(self) -> None:
        ref = reference("ore_ont_443.owl", "materialized-bottom")
        ref["consistent"] = False
        row = answer("ore_ont_443.owl", "different-consistent")
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("unknown", "unknown"))

    def test_collision_unsafe_fulliri_identity_is_authoritative(self) -> None:
        ontology = "ore_ont_3524.owl"
        ref = reference(ontology, "exact")
        ref.update(
            gold_kind="none",
            verdict="localname_not_applicable_fulliri_only",
            localname_identity_capable=False,
            localname_canonicalization_status="skipped_noninjective_projection",
        )
        row = answer(ontology, "exact")
        row.update(
            gold_kind="none",
            verdict="localname_not_applicable_fulliri_only",
            localname_identity_capable=False,
            localname_canonicalization_status="skipped_noninjective_projection",
        )
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("yes", "yes"))
        self.assertEqual(
            row["correctness_basis"], "same_job_fulliri_identity_to_konclude"
        )

    def test_collision_unsafe_mismatch_stays_unclassified(self) -> None:
        ontology = "ore_ont_15703.owl"
        ref = reference(ontology, "reference")
        ref.update(
            gold_kind="none",
            verdict="localname_not_applicable_fulliri_only",
            localname_identity_capable=False,
            localname_canonicalization_status="skipped_noninjective_projection",
        )
        row = answer(ontology, "different")
        row["verdict"] = "localname_not_applicable_fulliri_only"
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("unknown", "unknown"))

    def test_fulliri_exception_is_allowlisted(self) -> None:
        ontology = "ore_ont_99999.owl"
        ref = reference(ontology, "exact")
        ref.update(
            gold_kind="none",
            verdict="localname_not_applicable_fulliri_only",
            localname_identity_capable=False,
            localname_canonicalization_status="skipped_noninjective_projection",
        )
        row = answer(ontology, "exact")
        row["verdict"] = "localname_not_applicable_fulliri_only"
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("unknown", "unknown"))

    def test_konclude_reference_scores_itself_on_fulliri_only_input(self) -> None:
        ontology = "ore_ont_3524.owl"
        ref = reference(ontology, "exact")
        ref.update(
            gold_kind="none",
            verdict="localname_not_applicable_fulliri_only",
            localname_identity_capable=False,
            localname_canonicalization_status="skipped_noninjective_projection",
        )
        classify_correctness(ref, ref)
        self.assertEqual((ref["sound"], ref["complete"]), ("yes", "yes"))
        self.assertEqual(
            ref["correctness_basis"], "same_job_fulliri_konclude_reference"
        )

    def test_reference_identity_comes_from_arm_not_gold_kind(self) -> None:
        ref = reference("ore_ont_1.owl", "exact")
        ref["gold_kind"] = "konclude"
        ref["arm"] = "hermit"
        row = answer("ore_ont_1.owl", "exact")
        classify_correctness(row, ref)
        self.assertEqual((row["sound"], row["complete"]), ("yes", "yes"))
        self.assertEqual(row["correctness_basis"], "frozen_konclude_signature")


if __name__ == "__main__":
    unittest.main()
