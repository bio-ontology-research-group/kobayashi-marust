#!/usr/bin/env python3
"""Bind five historical selected routes to three exact-source rebuilds."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import tempfile


TARGETS = {
    "ore_ont_541.owl": {
        "route": "production_all",
        "candidate": "a639ab5",
        "commit": "a639ab59bfb20b04f0131a2b7b7cb727117a936b",
        "historical_binary": (
            "8771789c1afe5e80471caa9f7ed263eab2ab09af48673d1cb3f6b7ec0aa6284d"
        ),
        "historical_source_revision": "candidate-a639ab5",
    },
    "ore_ont_7409.owl": {
        "route": "production_all",
        "candidate": "a0d0148816c5",
        "commit": "a0d0148816c560f79b8ed12a762feef5f0401056",
        "historical_binary": (
            "60f147d5af3d300895fdad3eb41fff70443dff060bdac8fe7e3b2a434302acd9"
        ),
        "historical_source_revision": "candidate-a0d0148816c5",
    },
    "ore_ont_7914.owl": {
        "route": "production_all",
        "candidate": "a068059",
        "commit": "a0680597525b72b9d1d2c22e5d8f4b9820d8f401",
        "historical_binary": (
            "86eb38310683ab964d88ed87a86b61811fb6e2debc843f2c91c784c4bf535230"
        ),
        "historical_source_revision": "candidate-a068059",
    },
    "ore_ont_12653.owl": {
        "route": "production_all",
        "candidate": "a068059",
        "commit": "a0680597525b72b9d1d2c22e5d8f4b9820d8f401",
        "historical_binary": (
            "86eb38310683ab964d88ed87a86b61811fb6e2debc843f2c91c784c4bf535230"
        ),
        "historical_source_revision": "candidate-a068059",
    },
    "ore_ont_16462.owl": {
        "route": "production_all",
        "candidate": "a0d0148816c5",
        "commit": "a0d0148816c560f79b8ed12a762feef5f0401056",
        "historical_binary": (
            "60f147d5af3d300895fdad3eb41fff70443dff060bdac8fe7e3b2a434302acd9"
        ),
        "historical_source_revision": "candidate-a0d0148816c5",
    },
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--selected-registry", type=Path, required=True)
    parser.add_argument("--selected-registry-sha256", required=True)
    parser.add_argument("--candidate-capsules", type=Path, required=True)
    parser.add_argument("--candidate-capsules-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    return parser.parse_args()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def runtime_fields(path: Path) -> dict[str, str]:
    return {row["field"]: row["value"] for row in read_tsv(path)}


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w",
        encoding="utf-8",
        dir=path.parent,
        prefix=path.name + ".tmp.",
        delete=False,
    ) as handle:
        temporary = Path(handle.name)
        json.dump(value, handle, indent=2, sort_keys=True)
        handle.write("\n")
    os.replace(temporary, path)


def verify_candidate(row: dict[str, str]) -> dict[str, bool]:
    binary = Path(row["binary"])
    peer = Path(row["peer_binary"])
    build_path = Path(row["build_receipt"])
    test_path = Path(row["test_receipt"])
    identity_path = Path(row["source_identity"])
    runtime_path = Path(row["runtime_summary"])
    build = read_json(build_path)
    tests = read_json(test_path)
    identity = read_json(identity_path)
    runtime = runtime_fields(runtime_path)
    outputs = build.get("outputs") or {}
    binary_sha = row["binary_sha256"]
    return {
        "binary": sha256_file(binary) == binary_sha,
        "peer": sha256_file(peer) == binary_sha,
        "binary_bytes": binary.read_bytes() == peer.read_bytes(),
        "build_receipt": sha256_file(build_path)
        == row["build_receipt_sha256"],
        "test_receipt": sha256_file(test_path)
        == row["test_receipt_sha256"],
        "source_identity": sha256_file(identity_path)
        == row["source_identity_sha256"],
        "runtime_summary": sha256_file(runtime_path)
        == row["runtime_summary_sha256"],
        "build_verified": build.get("status") == "verified_reproducible",
        "build_identical": outputs.get("byte_identical") is True,
        "build_a": outputs.get("build_a_sha256") == binary_sha,
        "build_b": outputs.get("build_b_sha256") == binary_sha,
        "build_source": (build.get("source") or {}).get("manifest_sha256")
        == row["source_manifest_sha256"],
        "tests_verified": tests.get("status") == "verified_full_tests",
        "tests_pass": tests.get("failed") == 0
        and tests.get("return_code") == 0
        and tests.get("passed") == int(row["passed_tests"]),
        "tests_bind_build": tests.get("capsule_build_receipt_sha256")
        == row["build_receipt_sha256"],
        "identity_verified": identity.get("status")
        == "verified_exact_git_source",
        "identity_commit": identity.get("commit") == row["commit"],
        "identity_archive": identity.get("git_archive_sha256")
        == row["capsule_git_archive_sha256"],
        "identity_retained_archive": identity.get(
            "retained_git_archive_sha256"
        )
        == row["retained_git_archive_sha256"],
        "identity_source": identity.get("source_manifest_sha256")
        == row["source_manifest_sha256"],
        "runtime_captured": runtime.get("status")
        == "captured_for_later_independent_recheck",
        "runtime_binary": runtime.get("binary_sha256") == binary_sha,
        "runtime_source": runtime.get("source_manifest_sha256")
        == row["source_manifest_sha256"],
        "runtime_manifest": runtime.get("runtime_library_manifest_sha256")
        == row["runtime_manifest_sha256"],
    }


def main() -> int:
    args = parse_args()
    if sha256_file(args.selected_registry) != args.selected_registry_sha256:
        raise SystemExit("selected registry differs from its pinned SHA-256")
    if sha256_file(args.candidate_capsules) != args.candidate_capsules_sha256:
        raise SystemExit("candidate capsule registry differs from its pinned hash")
    selected = read_tsv(args.selected_registry)
    if len(selected) != 592:
        raise SystemExit(f"selected registry has {len(selected)} rows, expected 592")
    by_ontology = {row["ontology"]: row for row in selected}
    if len(by_ontology) != len(selected):
        raise SystemExit("selected registry repeats ontology names")
    candidates = read_tsv(args.candidate_capsules)
    if len(candidates) != 3:
        raise SystemExit("candidate capsule registry must contain three rows")
    by_candidate = {row["candidate"]: row for row in candidates}
    if len(by_candidate) != len(candidates):
        raise SystemExit("candidate capsule registry repeats candidate labels")
    expected_candidates = {target["candidate"] for target in TARGETS.values()}
    if set(by_candidate) != expected_candidates:
        raise SystemExit("candidate capsule registry has unexpected labels")

    candidate_checks = {}
    for label, candidate in by_candidate.items():
        checks = verify_candidate(candidate)
        if not all(checks.values()):
            raise SystemExit(
                f"candidate {label} failed checks: "
                f"{[key for key, value in checks.items() if not value]}"
            )
        candidate_checks[label] = checks

    extra_fields = [
        "historical_binary_sha256",
        "historical_binary_locator",
        "historical_source_revision",
        "historical_route_environment",
        "historical_invocation",
        "rebuild_candidate",
        "rebuild_source_commit",
        "rebuild_capsule_git_archive_sha256",
        "rebuild_retained_git_archive_sha256",
        "rebuild_source_manifest_sha256",
        "rebuild_build_receipt_sha256",
        "rebuild_test_receipt_sha256",
        "rebuild_source_identity_sha256",
        "rebuild_runtime_manifest_sha256",
        "selected_registry_sha256",
    ]
    output_rows = []
    for ontology, target in TARGETS.items():
        original = by_ontology.get(ontology)
        if original is None:
            raise SystemExit(f"selected registry lacks {ontology}")
        if (
            original["state"] != "exact_gold"
            or original["route"] != target["route"]
            or original["route_environment"] != "KM_ROUTE=production_all"
            or original["binary_sha256"] != target["historical_binary"]
            or original["source_revision"]
            != target["historical_source_revision"]
        ):
            raise SystemExit(f"historical route identity changed for {ontology}")
        candidate = by_candidate[target["candidate"]]
        if candidate["commit"] != target["commit"]:
            raise SystemExit(f"candidate commit changed for {ontology}")
        row = dict(original)
        binary = candidate["binary"]
        route_environment = original["route_environment"]
        row.update(
            binary_sha256=candidate["binary_sha256"],
            binary_locator=f"ibex:{binary}",
            source_revision=f"git:{target['commit']}",
            invocation=(
                f"env {route_environment} $KM_BIN classify "
                f"$ORE_CORPUS/{ontology}"
            ),
            evidence=(
                f"{original['evidence']} -> exact-source replay; "
                f"build_receipt_sha256={candidate['build_receipt_sha256']}; "
                f"source_identity_sha256={candidate['source_identity_sha256']}"
            ),
            notes=(
                f"{original['notes']} Historical executable "
                f"{target['historical_binary']} is provenance only and is not "
                f"executed. Replay uses two byte-identical builds from exact "
                f"commit {target['commit']}."
            ),
            historical_binary_sha256=original["binary_sha256"],
            historical_binary_locator=original["binary_locator"],
            historical_source_revision=original["source_revision"],
            historical_route_environment=original["route_environment"],
            historical_invocation=original["invocation"],
            rebuild_candidate=target["candidate"],
            rebuild_source_commit=target["commit"],
            rebuild_capsule_git_archive_sha256=candidate[
                "capsule_git_archive_sha256"
            ],
            rebuild_retained_git_archive_sha256=candidate[
                "retained_git_archive_sha256"
            ],
            rebuild_source_manifest_sha256=candidate[
                "source_manifest_sha256"
            ],
            rebuild_build_receipt_sha256=candidate[
                "build_receipt_sha256"
            ],
            rebuild_test_receipt_sha256=candidate["test_receipt_sha256"],
            rebuild_source_identity_sha256=candidate[
                "source_identity_sha256"
            ],
            rebuild_runtime_manifest_sha256=candidate[
                "runtime_manifest_sha256"
            ],
            selected_registry_sha256=args.selected_registry_sha256,
        )
        output_rows.append(row)

    fieldnames = list(selected[0]) + extra_fields
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)
    receipt = {
        "schema_version": 1,
        "status": "source_bound_exact_candidate_replay_registry",
        "rows": len(output_rows),
        "ontologies": list(TARGETS),
        "targets": TARGETS,
        "generator_sha256": sha256_file(Path(__file__)),
        "selected_registry_sha256": args.selected_registry_sha256,
        "candidate_capsules_sha256": args.candidate_capsules_sha256,
        "candidate_checks": candidate_checks,
        "output_sha256": sha256_file(args.output),
    }
    atomic_json(args.receipt, receipt)
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
