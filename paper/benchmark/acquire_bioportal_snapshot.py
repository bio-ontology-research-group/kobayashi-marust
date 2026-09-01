#!/usr/bin/env python3
"""Freeze the predeclared BioPortal candidate universe and source payloads.

The API key is read only from BIOPORTAL_API_KEY.  It is sent in an Authorization
header and is never written to a URL, receipt, manifest, or log.
"""

from __future__ import annotations

import argparse
import csv
from datetime import date, datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import time
from typing import Any
from urllib.error import HTTPError, URLError
from urllib.parse import quote, urljoin, urlsplit, urlunsplit
from urllib.request import Request, urlopen


API = "https://data.bioontology.org/"
USER_AGENT = "KM-paper-corpus-freezer/1.0"
FIELDS = (
    "acronym", "name", "submission_id", "released", "ontology_language",
    "source_sha256", "bytes", "media_type", "download_endpoint",
    "final_url", "final_url_query_sha256", "retrieved_utc", "license",
    "license_basis", "eligible",
    "exclusion_reason", "metadata_sha256",
)


def scalar_tail(value: Any) -> str:
    if isinstance(value, dict):
        value = value.get("acronym") or value.get("@id") or value.get("id") or ""
    if not isinstance(value, str):
        return ""
    return value.rstrip("/").rsplit("/", 1)[-1].upper()


def parse_day(value: Any) -> date | None:
    if not isinstance(value, str) or not value.strip():
        return None
    text = value.strip().replace("Z", "+00:00")
    try:
        return datetime.fromisoformat(text).date()
    except ValueError:
        try:
            return date.fromisoformat(text[:10])
        except ValueError:
            return None


def choose_submission(submissions: list[dict[str, Any]], cutoff: date) -> dict[str, Any] | None:
    candidates = []
    for submission in submissions:
        identifier = submission.get("submissionId")
        released = parse_day(submission.get("released"))
        if not isinstance(identifier, int) or released is None or released > cutoff:
            continue
        if scalar_tail(submission.get("hasOntologyLanguage")) != "OWL":
            continue
        candidates.append((released, identifier, submission))
    return max(candidates, default=(None, None, None))[-1]


def metadata_exclusion(ontology: dict[str, Any]) -> str:
    if ontology.get("viewOf"):
        return "ontology_view"
    if ontology.get("summaryOnly") is True:
        return "summary_only"
    if ontology.get("viewingRestriction"):
        return "viewing_restricted"
    if scalar_tail(ontology.get("ontologyType")) == "UMLS":
        return "restricted_umls_derived"
    return ""


def validate_payload(payload: bytes, media_type: str) -> str:
    if not payload:
        return "zero_byte_payload"
    prefix = payload[:4096].lstrip().lower()
    lowered_type = media_type.lower()
    if b"<html" in prefix or b"<!doctype html" in prefix or "text/html" in lowered_type:
        return "html_or_authentication_payload"
    if (prefix.startswith(b"{") or prefix.startswith(b"[")) and "json" in lowered_type:
        return "json_or_authentication_payload"
    return ""


def sanitise_final_url(value: str) -> tuple[str, str]:
    parts = urlsplit(value)
    clean = urlunsplit((parts.scheme, parts.netloc, parts.path, "", ""))
    query_digest = hashlib.sha256(parts.query.encode("utf-8")).hexdigest() if parts.query else ""
    return clean, query_digest


def read_tsv(path: Path | None) -> list[dict[str, str]]:
    if path is None:
        return []
    with path.open(encoding="utf-8", newline="") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


def source_digests(rows: list[dict[str, str]]) -> set[str]:
    result = {row.get("source_sha256") or row.get("sha256") or "" for row in rows} - {""}
    if rows and not result:
        raise ValueError("source manifest contains no SHA-256 digests")
    if any(not digest or len(digest) != 64 for digest in result):
        raise ValueError("invalid source SHA-256 in manifest")
    return result


class Client:
    def __init__(self, key: str, retries: int = 4) -> None:
        self.key = key
        self.retries = retries

    def get(self, endpoint: str, accept: str) -> tuple[bytes, str, str]:
        url = urljoin(API, endpoint)
        request = Request(url, headers={
            "Authorization": f"apikey token={self.key}",
            "Accept": accept,
            "User-Agent": USER_AGENT,
        })
        for attempt in range(self.retries):
            try:
                with urlopen(request, timeout=180) as response:
                    return response.read(), response.headers.get_content_type(), response.geturl()
            except HTTPError as error:
                if error.code not in {429, 500, 502, 503, 504} or attempt + 1 == self.retries:
                    raise
            except URLError:
                if attempt + 1 == self.retries:
                    raise
            time.sleep(2 ** attempt)
        raise AssertionError("unreachable")

    def json(self, endpoint: str) -> Any:
        payload, _, _ = self.get(endpoint, "application/json")
        return json.loads(payload)

    def download(self, endpoint: str, temporary: Path) -> dict[str, Any]:
        url = urljoin(API, endpoint)
        request = Request(url, headers={
            "Authorization": f"apikey token={self.key}",
            "Accept": "application/octet-stream",
            "User-Agent": USER_AGENT,
        })
        for attempt in range(self.retries):
            try:
                digest = hashlib.sha256(); size = 0; prefix = bytearray()
                temporary.parent.mkdir(parents=True, exist_ok=True)
                with urlopen(request, timeout=180) as response, temporary.open("wb") as stream:
                    media_type = response.headers.get_content_type()
                    final_url = response.geturl()
                    while chunk := response.read(8 * 1024 * 1024):
                        stream.write(chunk); digest.update(chunk); size += len(chunk)
                        if len(prefix) < 4096:
                            prefix.extend(chunk[:4096 - len(prefix)])
                return {"source_sha256": digest.hexdigest(), "bytes": size,
                        "media_type": media_type, "final_url": final_url,
                        "prefix": bytes(prefix)}
            except HTTPError as error:
                temporary.unlink(missing_ok=True)
                if error.code not in {429, 500, 502, 503, 504} or attempt + 1 == self.retries:
                    raise
            except URLError:
                temporary.unlink(missing_ok=True)
                if attempt + 1 == self.retries:
                    raise
            time.sleep(2 ** attempt)
        raise AssertionError("unreachable")


def write_atomic(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(str(path) + ".part")
    temporary.write_bytes(payload)
    temporary.replace(path)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(8 * 1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def resume_payload(source: Path, receipt: Path, acronym: str,
                   submission_id: int, endpoint: str) -> dict[str, Any] | None:
    if not source.is_file() or not receipt.is_file():
        return None
    try:
        record = json.loads(receipt.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    required = {"schema", "acronym", "submission_id", "download_endpoint",
                "source_sha256", "bytes", "media_type", "final_url",
                "final_url_query_sha256", "retrieved_utc", "terminal"}
    if not required.issubset(record) or record["schema"] != 1 \
            or record["terminal"] != "complete" or record["acronym"] != acronym \
            or record["submission_id"] != submission_id \
            or record["download_endpoint"] != endpoint:
        return None
    with source.open("rb") as stream:
        prefix = stream.read(4096)
    if source.stat().st_size != record["bytes"] \
            or sha256_file(source) != record["source_sha256"] \
            or validate_payload(prefix, record["media_type"]):
        return None
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", required=True, type=Path)
    parser.add_argument("--snapshot-date", default="2026-08-30", type=date.fromisoformat)
    parser.add_argument("--obo-manifest", required=True, type=Path)
    parser.add_argument("--license-decisions", type=Path,
                        help="TSV: acronym, decision(include|exclude), license, basis")
    args = parser.parse_args()

    key = os.environ.get("BIOPORTAL_API_KEY", "")
    if not key:
        raise SystemExit("BIOPORTAL_API_KEY is required and must not be passed on the command line")
    client = Client(key)
    root = args.output_root
    metadata_dir, source_dir = root / "metadata", root / "sources"
    acquisition_dir = root / "acquisition-receipts"
    metadata_dir.mkdir(parents=True, exist_ok=True); source_dir.mkdir(parents=True, exist_ok=True)
    acquisition_dir.mkdir(parents=True, exist_ok=True)

    obo_digests = source_digests(read_tsv(args.obo_manifest))
    decisions = {row["acronym"].upper(): row for row in read_tsv(args.license_decisions)}
    if len(decisions) != len(read_tsv(args.license_decisions)):
        raise ValueError("duplicate license decision")

    ontologies = client.json("ontologies?include=all")
    if not isinstance(ontologies, list):
        raise ValueError("BioPortal ontology collection is not a JSON list")
    write_atomic(root / "ontologies.json", json.dumps(ontologies, sort_keys=True,
                 indent=2).encode("utf-8") + b"\n")

    rows: list[dict[str, str]] = []
    seen_payloads: set[str] = set()
    for ontology in sorted(ontologies, key=lambda item: str(item.get("acronym", ""))):
        acronym = str(ontology.get("acronym", "")).upper()
        if not acronym or any(character not in "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for character in acronym):
            raise ValueError(f"unsafe or absent acronym: {acronym!r}")
        row = {field: "" for field in FIELDS}
        row.update(acronym=acronym, name=str(ontology.get("name", "")), eligible="false")
        exclusion = metadata_exclusion(ontology)
        submissions = client.json(f"ontologies/{quote(acronym)}/submissions?include=all")
        metadata_blob = json.dumps({"ontology": ontology, "submissions": submissions},
                                   sort_keys=True, indent=2).encode("utf-8") + b"\n"
        write_atomic(metadata_dir / f"{acronym}.json", metadata_blob)
        row["metadata_sha256"] = hashlib.sha256(metadata_blob).hexdigest()
        selected = choose_submission(submissions if isinstance(submissions, list) else [],
                                     args.snapshot_date)
        if selected is None:
            row["exclusion_reason"] = exclusion or "no_public_owl_submission_at_cutoff"
            rows.append(row); continue
        row.update(submission_id=str(selected["submissionId"]),
                   released=str(selected.get("released", "")),
                   ontology_language=scalar_tail(selected.get("hasOntologyLanguage")))
        if exclusion:
            row["exclusion_reason"] = exclusion; rows.append(row); continue

        endpoint = f"ontologies/{quote(acronym)}/submissions/{selected['submissionId']}/download"
        source_path = source_dir / f"{acronym}.source"
        receipt_path = acquisition_dir / f"{acronym}.json"
        acquisition = resume_payload(source_path, receipt_path, acronym,
                                     selected["submissionId"], endpoint)
        if acquisition is None:
            download_part = Path(str(source_path) + ".download.part")
            try:
                downloaded = client.download(endpoint, download_part)
            except (HTTPError, URLError) as error:
                row["exclusion_reason"] = f"download_failed_{type(error).__name__}"
                rows.append(row); continue
            digest = downloaded["source_sha256"]
            media_type = downloaded["media_type"]
            invalid = validate_payload(downloaded["prefix"], media_type)
            if invalid:
                download_part.unlink(missing_ok=True)
                row.update(source_sha256=digest, bytes=str(downloaded["bytes"]), media_type=media_type,
                           download_endpoint=endpoint, exclusion_reason=invalid)
                rows.append(row); continue
            clean_url, query_digest = sanitise_final_url(downloaded["final_url"])
            retrieved = datetime.now(timezone.utc).isoformat()
            acquisition = {
                "schema": 1, "acronym": acronym,
                "submission_id": selected["submissionId"],
                "download_endpoint": endpoint, "source_sha256": digest,
                "bytes": downloaded["bytes"], "media_type": media_type,
                "final_url": clean_url, "final_url_query_sha256": query_digest,
                "retrieved_utc": retrieved, "terminal": "complete",
            }
            download_part.replace(source_path)
            write_atomic(receipt_path, json.dumps(acquisition, sort_keys=True,
                         indent=2).encode("utf-8") + b"\n")
        digest = acquisition["source_sha256"]
        row.update(source_sha256=digest, bytes=str(acquisition["bytes"]),
                   media_type=acquisition["media_type"], download_endpoint=endpoint,
                   final_url=acquisition["final_url"],
                   final_url_query_sha256=acquisition["final_url_query_sha256"],
                   retrieved_utc=acquisition["retrieved_utc"])
        if digest in obo_digests:
            row["exclusion_reason"] = "duplicate_of_obo_source"
        elif digest in seen_payloads:
            row["exclusion_reason"] = "duplicate_of_earlier_bioportal_source"
        else:
            seen_payloads.add(digest)
            decision = decisions.get(acronym)
            if decision is None:
                row["exclusion_reason"] = "license_decision_missing"
            elif decision.get("decision") == "exclude":
                row["exclusion_reason"] = "license_excluded"
                row["license"] = decision.get("license", "")
                row["license_basis"] = decision.get("basis", "")
            elif decision.get("decision") == "include" and decision.get("license") \
                    and decision.get("basis"):
                row.update(eligible="true", exclusion_reason="",
                           license=decision["license"], license_basis=decision["basis"])
            else:
                raise ValueError(f"invalid license decision for {acronym}")
        rows.append(row)

    manifest = root / f"bioportal-candidates-{args.snapshot_date.isoformat()}.tsv"
    temporary = Path(str(manifest) + ".part")
    with temporary.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=FIELDS, delimiter="\t")
        writer.writeheader(); writer.writerows(rows)
    temporary.replace(manifest)
    print(f"BIOPORTAL_FREEZE_OK\t{len(rows)}\t{sum(r['eligible']=='true' for r in rows)}")


if __name__ == "__main__":
    main()
