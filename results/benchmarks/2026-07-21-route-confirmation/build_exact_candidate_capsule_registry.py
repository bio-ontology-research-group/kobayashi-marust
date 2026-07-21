#!/usr/bin/env python3
"""Inventory and verify exact-source historical candidate capsules."""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import tempfile


CANDIDATES = {
    "a639ab5": {
        "commit": "a639ab59bfb20b04f0131a2b7b7cb727117a936b",
        "retained_source_archive_sha256": (
            "40a4eb56ee1efd85a56b14409a4cd95cf30308b6eec40963320351291ba92de8"
        ),
        "retained_git_archive_sha256": (
            "231ae05105ecc45dea7a5adb03bb81dd99859b8a46faf03bcf9516fad75b5a11"
        ),
        "capsule_git_archive_sha256": (
            "5e54967f9aba7f62de4d03ecfbb3c95656ee8d4fc5501502ee1eab1d8643f8ef"
        ),
    },
    "a068059": {
        "commit": "a0680597525b72b9d1d2c22e5d8f4b9820d8f401",
        "retained_source_archive_sha256": (
            "305d857b66420f43a208bee748a2c9ab545083ec626953345ac6bbf61fc88878"
        ),
        "retained_git_archive_sha256": (
            "bea13603606c26326cd16cf8b94ab2591531bd96a180ea660156003130c3df23"
        ),
        "capsule_git_archive_sha256": (
            "87683de45a2fa76ed9d22e6ce0782a49e8bbf5e0ad888d13f966281a740653d9"
        ),
    },
    "a0d0148816c5": {
        "commit": "a0d0148816c560f79b8ed12a762feef5f0401056",
        "retained_source_archive_sha256": (
            "34c46085d11715d5c6ad504fc3a20977917f3b453f07858f406d34ffbc8313b7"
        ),
        "retained_git_archive_sha256": (
            "59cebd88623b3ef1eb9c1ed325095f3e692ddf5165a475c9081af9012504162e"
        ),
        "capsule_git_archive_sha256": (
            "3c10d6952af35322bcaf67d7926a22f1f2c9536e431b980e9522a51a7ff2d2b7"
        ),
    },
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rebuild-root", type=Path, required=True)
    parser.add_argument("--build-set-receipt-sha256", required=True)
    parser.add_argument("--identity-dir", type=Path, required=True)
    parser.add_argument("--expected-source-verifier-sha256", required=True)
    parser.add_argument("--runtime-root", type=Path)
    parser.add_argument("--runtime-array-job-id")
    parser.add_argument("--expected-runtime-driver-sha256")
    parser.add_argument("--expected-ldd-sha256")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    return parser.parse_args()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))


def summary_fields(path: Path) -> dict[str, str]:
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


def main() -> int:
    args = parse_args()
    runtime_options = (
        args.runtime_root,
        args.runtime_array_job_id,
        args.expected_runtime_driver_sha256,
        args.expected_ldd_sha256,
    )
    if any(value is not None for value in runtime_options) and not all(
        value is not None for value in runtime_options
    ):
        raise SystemExit("runtime root and array job ID must be supplied together")
    if args.runtime_array_job_id is not None and not str(
        args.runtime_array_job_id
    ).isdigit():
        raise SystemExit("runtime array job ID must be numeric")

    root = args.rebuild_root.resolve()
    identity_dir = args.identity_dir.resolve()
    build_set_path = root / "build-set-receipt.json"
    if sha256_file(build_set_path) != args.build_set_receipt_sha256:
        raise SystemExit("build-set receipt differs from its pinned hash")
    build_set = load_json(build_set_path)
    build_rows = {
        row["label"]: row for row in build_set.get("candidates") or []
    }
    if (
        build_set.get("status") != "verified_sequential_reproducible_builds"
        or build_set.get("concurrent_builds") != 1
        or build_set.get("build_cpus") != 4
        or set(build_rows) != set(CANDIDATES)
    ):
        raise SystemExit("build-set receipt has an unexpected identity")

    fieldnames = [
        "candidate",
        "commit",
        "retained_source_archive_sha256",
        "retained_git_archive_sha256",
        "capsule_git_archive_sha256",
        "binary",
        "peer_binary",
        "binary_sha256",
        "source_manifest_sha256",
        "build_receipt",
        "build_receipt_sha256",
        "test_receipt",
        "test_receipt_sha256",
        "passed_tests",
        "source_identity",
        "source_identity_sha256",
        "runtime_summary",
        "runtime_summary_sha256",
        "runtime_manifest_sha256",
        "runtime_library_count",
        "runtime_array_job_id",
        "runtime_array_task_id",
    ]
    output_rows = []
    checks_by_candidate = {}
    for task_index, (label, expected) in enumerate(CANDIDATES.items()):
        capsule = root / "capsules" / label
        tests_dir = root / "tests" / label
        binary = capsule / "km-build-a"
        peer = capsule / "km-build-b"
        source_manifest = capsule / "source-files.sha256"
        build_receipt_path = capsule / "build-receipt.json"
        test_receipt_path = tests_dir / "test-receipt.json"
        identity_path = identity_dir / f"{label}-source-identity.json"
        build_receipt = load_json(build_receipt_path)
        test_receipt = load_json(test_receipt_path)
        identity = load_json(identity_path)
        binary_sha = sha256_file(binary)
        source_manifest_sha = sha256_file(source_manifest)
        build_receipt_sha = sha256_file(build_receipt_path)
        test_receipt_sha = sha256_file(test_receipt_path)
        identity_sha = sha256_file(identity_path)
        outputs = build_receipt.get("outputs") or {}
        build_row = build_rows[label]
        checks = {
            "build_set_commit": build_row.get("commit")
            == expected["commit"],
            "build_set_archive": build_row.get("git_archive_sha256")
            == expected["retained_git_archive_sha256"],
            "build_set_retained_archive": build_row.get(
                "retained_source_archive_sha256"
            )
            == expected["retained_source_archive_sha256"],
            "build_set_binary": build_row.get("binary_sha256")
            == binary_sha,
            "build_set_source": build_row.get("source_manifest_sha256")
            == source_manifest_sha,
            "build_set_receipt": build_row.get("build_receipt_sha256")
            == build_receipt_sha,
            "build_set_tests": build_row.get("test_receipt_sha256")
            == test_receipt_sha,
            "peer_binary": sha256_file(peer) == binary_sha,
            "binary_bytes": binary.read_bytes() == peer.read_bytes(),
            "build_verified": build_receipt.get("status")
            == "verified_reproducible",
            "build_identical": outputs.get("byte_identical") is True,
            "build_a": outputs.get("build_a_sha256") == binary_sha,
            "build_b": outputs.get("build_b_sha256") == binary_sha,
            "build_source": (build_receipt.get("source") or {}).get(
                "manifest_sha256"
            )
            == source_manifest_sha,
            "tests_verified": test_receipt.get("status")
            == "verified_full_tests",
            "tests_pass": test_receipt.get("failed") == 0
            and test_receipt.get("return_code") == 0
            and test_receipt.get("passed") == build_row.get("passed_tests"),
            "tests_bind_build": test_receipt.get(
                "capsule_build_receipt_sha256"
            )
            == build_receipt_sha,
            "identity_verified": identity.get("status")
            == "verified_exact_git_source",
            "identity_commit": identity.get("commit")
            == expected["commit"],
            "identity_git_archive": identity.get("git_archive_sha256")
            == expected["capsule_git_archive_sha256"],
            "identity_retained_archive": identity.get(
                "retained_source_archive_sha256"
            )
            == expected["retained_source_archive_sha256"],
            "identity_retained_git_archive": identity.get(
                "retained_git_archive_sha256"
            )
            == expected["retained_git_archive_sha256"],
            "identity_source": identity.get("source_manifest_sha256")
            == source_manifest_sha,
            "identity_build": identity.get("build_receipt_sha256")
            == build_receipt_sha,
            "identity_verifier": identity.get("verifier_sha256")
            == args.expected_source_verifier_sha256,
        }

        runtime_summary = ""
        runtime_summary_sha = ""
        runtime_manifest_sha = ""
        runtime_count = ""
        runtime_array_job_id = ""
        runtime_array_task_id = ""
        if args.runtime_root is not None:
            runtime_dir = (
                args.runtime_root.resolve()
                / f"exact-candidate-{label}-{args.runtime_array_job_id}-{task_index}"
            )
            runtime_summary_path = runtime_dir / "SUMMARY.tsv"
            runtime_manifest_path = runtime_dir / "runtime-files.sha256"
            runtime = summary_fields(runtime_summary_path)
            runtime_summary = str(runtime_summary_path)
            runtime_summary_sha = sha256_file(runtime_summary_path)
            runtime_manifest_sha = sha256_file(runtime_manifest_path)
            runtime_count = str(
                len(runtime_manifest_path.read_text(encoding="utf-8").splitlines())
            )
            runtime_array_job_id = str(args.runtime_array_job_id)
            runtime_array_task_id = str(task_index)
            checks.update(
                runtime_status=runtime.get("status")
                == "captured_for_later_independent_recheck",
                runtime_candidate=runtime.get("candidate") == label,
                runtime_commit=runtime.get("source_commit")
                == expected["commit"],
                runtime_binary=runtime.get("binary_sha256") == binary_sha,
                runtime_source=runtime.get("source_manifest_sha256")
                == source_manifest_sha,
                runtime_build=runtime.get("build_receipt_sha256")
                == build_receipt_sha,
                runtime_tests=runtime.get("test_receipt_sha256")
                == test_receipt_sha,
                runtime_identity=runtime.get("source_identity_sha256")
                == identity_sha,
                runtime_manifest=runtime.get(
                    "runtime_library_manifest_sha256"
                )
                == runtime_manifest_sha,
                runtime_count=runtime.get("runtime_library_count")
                == runtime_count,
                runtime_array_job=runtime.get("slurm_array_job_id")
                == str(args.runtime_array_job_id),
                runtime_array_task=runtime.get("slurm_array_task_id")
                == str(task_index),
                runtime_driver=runtime.get("driver_sha256")
                == args.expected_runtime_driver_sha256,
                runtime_ldd=runtime.get("ldd_sha256")
                == args.expected_ldd_sha256,
            )
        if not all(checks.values()):
            raise SystemExit(
                f"candidate {label} failed checks: "
                f"{[key for key, value in checks.items() if not value]}"
            )
        checks_by_candidate[label] = checks
        output_rows.append(
            {
                "candidate": label,
                "commit": expected["commit"],
                "retained_source_archive_sha256": expected[
                    "retained_source_archive_sha256"
                ],
                "retained_git_archive_sha256": expected[
                    "retained_git_archive_sha256"
                ],
                "capsule_git_archive_sha256": expected[
                    "capsule_git_archive_sha256"
                ],
                "binary": str(binary),
                "peer_binary": str(peer),
                "binary_sha256": binary_sha,
                "source_manifest_sha256": source_manifest_sha,
                "build_receipt": str(build_receipt_path),
                "build_receipt_sha256": build_receipt_sha,
                "test_receipt": str(test_receipt_path),
                "test_receipt_sha256": test_receipt_sha,
                "passed_tests": str(test_receipt.get("passed")),
                "source_identity": str(identity_path),
                "source_identity_sha256": identity_sha,
                "runtime_summary": runtime_summary,
                "runtime_summary_sha256": runtime_summary_sha,
                "runtime_manifest_sha256": runtime_manifest_sha,
                "runtime_library_count": runtime_count,
                "runtime_array_job_id": runtime_array_job_id,
                "runtime_array_task_id": runtime_array_task_id,
            }
        )

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, delimiter="\t")
        writer.writeheader()
        writer.writerows(output_rows)
    receipt = {
        "schema_version": 1,
        "status": (
            "source_bound_exact_candidate_capsules_with_runtime"
            if args.runtime_root is not None
            else "source_bound_exact_candidate_capsules"
        ),
        "rows": len(output_rows),
        "generator_sha256": sha256_file(Path(__file__)),
        "build_set_receipt_sha256": args.build_set_receipt_sha256,
        "expected_source_verifier_sha256": (
            args.expected_source_verifier_sha256
        ),
        "runtime_array_job_id": args.runtime_array_job_id or "",
        "expected_runtime_driver_sha256": (
            args.expected_runtime_driver_sha256 or ""
        ),
        "expected_ldd_sha256": args.expected_ldd_sha256 or "",
        "checks": checks_by_candidate,
        "output_sha256": sha256_file(args.output),
    }
    atomic_json(args.receipt, receipt)
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
