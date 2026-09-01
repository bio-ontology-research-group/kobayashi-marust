#!/usr/bin/env python3

from datetime import date
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from acquire_bioportal_snapshot import (
    choose_submission, metadata_exclusion, resume_payload, sanitise_final_url,
    source_digests,
    validate_payload,
)


class BioPortalAcquisitionTest(unittest.TestCase):
    def test_selects_latest_owl_submission_at_cutoff(self) -> None:
        submissions = [
            {"submissionId": 1, "released": "2025-01-01", "hasOntologyLanguage": "OWL"},
            {"submissionId": 2, "released": "2026-08-30T12:00:00Z",
             "hasOntologyLanguage": {"@id": "http://data.bioontology.org/formats/OWL"}},
            {"submissionId": 3, "released": "2026-08-31", "hasOntologyLanguage": "OWL"},
            {"submissionId": 4, "released": "2026-08-30", "hasOntologyLanguage": "SKOS"},
        ]
        self.assertEqual(choose_submission(submissions, date(2026, 8, 30))["submissionId"], 2)

    def test_exclusions_and_payload_rejection_are_fail_closed(self) -> None:
        self.assertEqual(metadata_exclusion({"viewOf": "X"}), "ontology_view")
        self.assertEqual(metadata_exclusion({"summaryOnly": True}), "summary_only")
        self.assertEqual(metadata_exclusion({"ontologyType": "http://x/UMLS"}),
                         "restricted_umls_derived")
        self.assertEqual(validate_payload(b"<html>login</html>", "text/html"),
                         "html_or_authentication_payload")
        self.assertEqual(validate_payload(b"Ontology(<x>)", "application/octet-stream"), "")
        clean, digest = sanitise_final_url("https://example.org/o.owl?apikey=secret")
        self.assertEqual(clean, "https://example.org/o.owl")
        self.assertEqual(len(digest), 64)

    def test_resume_requires_complete_source_bound_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source, receipt = root / "A.source", root / "A.json"
            payload = b"Ontology(<https://example.org/a>)"
            source.write_bytes(payload)
            record = {
                "schema": 1, "acronym": "A", "submission_id": 7,
                "download_endpoint": "ontologies/A/submissions/7/download",
                "source_sha256": hashlib.sha256(payload).hexdigest(),
                "bytes": len(payload), "media_type": "application/octet-stream",
                "final_url": "https://example.org/a.owl", "final_url_query_sha256": "",
                "retrieved_utc": "2026-08-30T00:00:00+00:00", "terminal": "complete",
            }
            receipt.write_text(json.dumps(record), encoding="utf-8")
            resumed = resume_payload(source, receipt, "A", 7, record["download_endpoint"])
            self.assertEqual(resumed["source_sha256"], record["source_sha256"])
            source.write_bytes(payload + b"corrupt")
            self.assertIsNone(resume_payload(source, receipt, "A", 7,
                                             record["download_endpoint"]))

    def test_obo_digest_schema_is_recognised(self) -> None:
        digest = "a" * 64
        self.assertEqual(source_digests([{"sha256": digest}]), {digest})
        self.assertEqual(source_digests([{"source_sha256": digest}]), {digest})
        with self.assertRaises(ValueError):
            source_digests([{"id": "missing"}])


if __name__ == "__main__":
    unittest.main()
