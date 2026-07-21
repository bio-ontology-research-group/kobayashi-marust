#!/usr/bin/env python3
"""Fresh, full-IRI validation of one documented ORE solve route.

Each Slurm array task reads one row from ``ontology-solve-routes.tsv``.  The
historical executable is never run: its row supplies only the semantic route
configuration to reconstruct.  A gold-exact claim is accepted only when a
twice-built, hash-pinned current KM executable finishes inside the documented
limits and its full-IRI taxonomy is identical to a fresh classification from
a twice-built official Konclude source capsule on the same allocation. The two
stale-Konclude-gold
inconsistency claims are checked against fresh HermiT runs on the same complete
ontology bytes.

The reasoners and the full-IRI canonicalizer run only on an IBEX compute node.
The script writes a small atomic JSON record after every phase so interrupted
array tasks are distinguishable from routes that were never attempted.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import traceback


EXACT = "exact_gold"
ADJUDICATED = "adjudicated_correct_stale_gold"
CLAIMED_STATES = {EXACT, ADJUDICATED}
EXTERNAL_WORKER_KEYS = {
    "KM_ENGINE_BIN",
    "KM_ELC_BIN",
    "KM_OFN_BIN",
    "KM_TABLEAU_BIN",
    "KM_HT_BIN",
}
LDD = Path("/usr/bin/ldd")
VALIDATOR_ENVIRONMENT_KEYS = {
    "PATH",
    "LC_ALL",
    "PYTHONHASHSEED",
    "SLURM_JOB_ID",
    "SLURM_ARRAY_JOB_ID",
    "SLURM_ARRAY_TASK_ID",
    "SLURM_CPUS_PER_TASK",
    "SLURM_TMPDIR",
    "TMPDIR",
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def canonical_json_sha256(value: object) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def validator_environment_checks() -> tuple[dict[str, str], dict[str, bool]]:
    environment = dict(os.environ)
    unexpected = sorted(set(environment) - VALIDATOR_ENVIRONMENT_KEYS)
    slurm_tmpdir = environment.get("SLURM_TMPDIR")
    return environment, {
        "path": environment.get("PATH") == "/usr/bin:/bin",
        "locale": environment.get("LC_ALL") == "C",
        "python_hash_seed": environment.get("PYTHONHASHSEED") == "0",
        "slurm_job": bool(environment.get("SLURM_JOB_ID")),
        "slurm_cpus": environment.get("SLURM_CPUS_PER_TASK") == "16",
        "temporary_directory": not slurm_tmpdir
        or environment.get("TMPDIR") == slurm_tmpdir,
        "no_unexpected_variables": not unexpected,
    }


def konclude_runtime_identity(
    *,
    binary: Path,
    library_dir: Path,
    expected_ldd_sha256: str,
) -> dict:
    """Resolve every library under the exact source-built Konclude route."""
    if not library_dir.is_absolute() or not library_dir.is_dir():
        raise ValueError(f"invalid Konclude library directory: {library_dir}")
    environment = {
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "PYTHONHASHSEED": "0",
        "LD_LIBRARY_PATH": str(library_dir),
    }
    identity = executable_runtime_identity(
        binary=binary,
        environment=environment,
        expected_ldd_sha256=expected_ldd_sha256,
    )
    identity.update(
        {
            "schema_version": 2,
            "library_directory": str(library_dir),
        }
    )
    return identity


def verify_sha256_manifest(
    path: Path, *, expected_sha256: str, expected_count: int
) -> tuple[list[dict[str, str]], dict[str, bool]]:
    """Verify a sorted sha256sum manifest and every file named by it."""
    lines = path.read_text(encoding="utf-8").splitlines()
    entries: list[dict[str, str]] = []
    parsed = True
    for line in lines:
        digest, separator, filename = line.partition("  ")
        if (
            separator != "  "
            or re.fullmatch(r"[0-9a-f]{64}", digest) is None
            or not filename.startswith("/")
        ):
            parsed = False
            continue
        entries.append({"path": filename, "sha256": digest})
    paths = [entry["path"] for entry in entries]
    files_match = parsed and all(
        Path(entry["path"]).is_file()
        and sha256_file(Path(entry["path"])) == entry["sha256"]
        for entry in entries
    )
    checks = {
        "manifest_sha256": sha256_file(path) == expected_sha256,
        "manifest_count": len(lines) == expected_count,
        "manifest_parsed": parsed and len(entries) == len(lines),
        "manifest_sorted_unique": paths == sorted(set(paths)),
        "manifest_files_match": files_match,
    }
    return entries, checks


def executable_runtime_identity(
    *, binary: Path, environment: dict[str, str], expected_ldd_sha256: str
) -> dict:
    """Hash the direct dynamic-library closure reported by a pinned ldd."""
    if sha256_file(LDD) != expected_ldd_sha256:
        raise ValueError("/usr/bin/ldd differs from the pinned runtime tool")
    completed = subprocess.run(
        [str(LDD), str(binary)],
        cwd="/",
        env=environment,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise RuntimeError(
            "pinned ldd failed: "
            + completed.stderr.decode("utf-8", errors="replace")[-4000:]
        )
    paths: set[Path] = set()
    unresolved: list[str] = []
    for raw_line in completed.stdout.decode(
        "utf-8", errors="replace"
    ).splitlines():
        fields = raw_line.strip().split()
        if not fields:
            continue
        if len(fields) >= 3 and fields[1] == "=>":
            if fields[2] == "not":
                unresolved.append(raw_line.strip())
            elif fields[2].startswith("/"):
                paths.add(Path(fields[2]))
        elif fields[0].startswith("/"):
            paths.add(Path(fields[0]))
    if unresolved or not paths:
        raise RuntimeError(
            f"invalid runtime closure: unresolved={unresolved}, paths={len(paths)}"
        )
    entries = []
    manifest = bytearray()
    for path in sorted(paths, key=lambda item: str(item)):
        digest = sha256_file(path)
        entries.append({"path": str(path), "sha256": digest})
        manifest.extend(f"{digest}  {path}\n".encode("utf-8"))
    return {
        "binary": str(binary),
        "binary_sha256": sha256_file(binary),
        "working_directory": "/",
        "environment": environment,
        "ldd_sha256": sha256_file(LDD),
        "ldd_stdout_sha256": hashlib.sha256(completed.stdout).hexdigest(),
        "ldd_stderr_sha256": hashlib.sha256(completed.stderr).hexdigest(),
        "runtime_library_count": len(entries),
        "runtime_libraries": entries,
        "runtime_library_manifest_sha256": hashlib.sha256(manifest).hexdigest(),
    }


def verify_hermit_build_receipt(
    *,
    receipt_path: Path,
    expected_receipt_sha256: str,
    driver: Path,
    expected_driver_sha256: str,
    oracle: Path,
    expected_oracle_sha256: str,
    source: Path,
    expected_source_sha256: str,
    java: Path,
    expected_java_sha256: str,
    expected_javac_sha256: str,
    classpath: str,
    classpath_manifest: Path,
    expected_classpath_manifest_sha256: str,
    expected_classpath_count: int,
    jdk_manifest: Path,
    expected_jdk_manifest_sha256: str,
    expected_jdk_count: int,
    jdk_symlinks: Path,
    expected_jdk_symlinks_sha256: str,
    expected_jdk_symlink_count: int,
) -> tuple[dict, dict[str, bool]]:
    """Validate the twice-built Java oracle and all hidden Java inputs."""
    receipt = load_json(receipt_path)
    outputs = receipt.get("outputs") or {}
    receipt_source = receipt.get("source") or {}
    toolchain = receipt.get("toolchain") or {}
    receipt_classpath = receipt.get("classpath") or {}
    classpath_entries, classpath_checks = verify_sha256_manifest(
        classpath_manifest,
        expected_sha256=expected_classpath_manifest_sha256,
        expected_count=expected_classpath_count,
    )
    jdk_entries, jdk_checks = verify_sha256_manifest(
        jdk_manifest,
        expected_sha256=expected_jdk_manifest_sha256,
        expected_count=expected_jdk_count,
    )

    jar_parents = {str(Path(entry["path"]).parent) for entry in classpath_entries}
    expected_classpath = ""
    if len(jar_parents) == 1:
        expected_classpath = f"{oracle.parent}:{next(iter(jar_parents))}/*"
    jdk_root = java.parent.parent
    symlink_lines = jdk_symlinks.read_text(encoding="utf-8").splitlines()
    symlinks_parsed = True
    symlinks_match = True
    symlink_names: list[str] = []
    for line in symlink_lines:
        relative, separator, target = line.partition("\t")
        if not separator or not relative or relative.startswith("/"):
            symlinks_parsed = False
            continue
        symlink_names.append(relative)
        link = jdk_root / relative
        if not link.is_symlink() or os.readlink(link) != target:
            symlinks_match = False

    checks = {
        "receipt_sha256": sha256_file(receipt_path)
        == expected_receipt_sha256,
        "receipt_status": receipt.get("status") == "verified_reproducible",
        "build_driver_sha256": receipt.get("driver_sha256")
        == expected_driver_sha256,
        "build_driver_file_sha256": sha256_file(driver)
        == expected_driver_sha256,
        "source_sha256": sha256_file(source) == expected_source_sha256,
        "receipt_source_path": Path(str(receipt_source.get("path", "")))
        == source,
        "receipt_source_sha256": receipt_source.get("sha256")
        == expected_source_sha256,
        "oracle_sha256": sha256_file(oracle) == expected_oracle_sha256,
        "twice_built_byte_identical": outputs.get("byte_identical") is True,
        "build_a_sha256": outputs.get("build_a_sha256")
        == expected_oracle_sha256,
        "build_b_sha256": outputs.get("build_b_sha256")
        == expected_oracle_sha256,
        "output_sha256": outputs.get("binary_sha256")
        == expected_oracle_sha256,
        "executed_build_a": Path(str(outputs.get("build_a", ""))) == oracle,
        "java_sha256": sha256_file(java) == expected_java_sha256,
        "receipt_java_sha256": toolchain.get("java_sha256")
        == expected_java_sha256,
        "receipt_javac_sha256": toolchain.get("javac_sha256")
        == expected_javac_sha256,
        "classpath_string": classpath == expected_classpath,
        "receipt_classpath_manifest": Path(
            str(receipt_classpath.get("manifest", ""))
        )
        == classpath_manifest,
        "receipt_classpath_sha256": receipt_classpath.get("manifest_sha256")
        == expected_classpath_manifest_sha256,
        "receipt_classpath_count": receipt_classpath.get("file_count")
        == expected_classpath_count,
        "receipt_jdk_manifest": Path(
            str(toolchain.get("jdk_file_manifest", ""))
        )
        == jdk_manifest,
        "receipt_jdk_manifest_sha256": toolchain.get(
            "jdk_file_manifest_sha256"
        )
        == expected_jdk_manifest_sha256,
        "receipt_jdk_count": toolchain.get("jdk_file_count")
        == expected_jdk_count,
        "receipt_jdk_symlinks": Path(
            str(toolchain.get("jdk_symlink_manifest", ""))
        )
        == jdk_symlinks,
        "receipt_jdk_symlinks_sha256": toolchain.get(
            "jdk_symlink_manifest_sha256"
        )
        == expected_jdk_symlinks_sha256,
        "receipt_jdk_symlink_count": toolchain.get("jdk_symlink_count")
        == expected_jdk_symlink_count,
        "jdk_symlink_manifest_sha256": sha256_file(jdk_symlinks)
        == expected_jdk_symlinks_sha256,
        "jdk_symlink_manifest_count": len(symlink_lines)
        == expected_jdk_symlink_count,
        "jdk_symlink_manifest_parsed": symlinks_parsed,
        "jdk_symlink_manifest_sorted_unique": symlink_names
        == sorted(set(symlink_names)),
        "jdk_symlinks_match": symlinks_match,
    }
    checks.update(
        {f"classpath_{key}": value for key, value in classpath_checks.items()}
    )
    checks.update({f"jdk_{key}": value for key, value in jdk_checks.items()})
    return receipt, checks


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--row-index", type=int, required=True)
    parser.add_argument(
        "--expected-registry-row-count",
        type=int,
        default=592,
        help=(
            "fail closed unless the registry has exactly this many rows; "
            "the default binds the complete ORE registry"
        ),
    )
    parser.add_argument("--km-root", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--fingerprint", type=Path, required=True)
    parser.add_argument("--validation-driver", type=Path, required=True)
    parser.add_argument("--validation-driver-sha256", required=True)
    parser.add_argument(
        "--validation-protocol",
        default="reproducible-current-selected-full-iri-v2",
        help="stable protocol label recorded in every result",
    )
    parser.add_argument(
        "--route-observation-policy",
        choices=("runtime-trace", "closed-manual-environment"),
        default="runtime-trace",
        help=(
            "require the current runtime trace, or for pre-trace historical "
            "sources identify a manual route by its complete closed KM_* "
            "environment"
        ),
    )
    parser.add_argument("--konclude", type=Path, required=True)
    parser.add_argument("--konclude-sha256", required=True)
    parser.add_argument("--konclude-library-dir", type=Path, required=True)
    parser.add_argument("--konclude-runtime-count", type=int, required=True)
    parser.add_argument("--konclude-runtime-stream-sha256", required=True)
    parser.add_argument("--konclude-build-receipt", type=Path, required=True)
    parser.add_argument("--konclude-build-receipt-sha256", required=True)
    parser.add_argument("--konclude-source-manifest-sha256", required=True)
    parser.add_argument("--konclude-build-driver", type=Path, required=True)
    parser.add_argument("--konclude-build-driver-sha256", required=True)
    parser.add_argument("--ldd-sha256", required=True)
    parser.add_argument("--hermit-java", type=Path, required=True)
    parser.add_argument("--hermit-java-sha256", required=True)
    parser.add_argument("--hermit-javac-sha256", required=True)
    parser.add_argument("--hermit-oracle", type=Path, required=True)
    parser.add_argument("--hermit-oracle-sha256", required=True)
    parser.add_argument("--hermit-source", type=Path, required=True)
    parser.add_argument("--hermit-source-sha256", required=True)
    parser.add_argument("--hermit-classpath", required=True)
    parser.add_argument("--hermit-classpath-manifest", type=Path, required=True)
    parser.add_argument("--hermit-classpath-manifest-sha256", required=True)
    parser.add_argument("--hermit-classpath-count", type=int, required=True)
    parser.add_argument("--hermit-jdk-manifest", type=Path, required=True)
    parser.add_argument("--hermit-jdk-manifest-sha256", required=True)
    parser.add_argument("--hermit-jdk-count", type=int, required=True)
    parser.add_argument("--hermit-jdk-symlinks", type=Path, required=True)
    parser.add_argument("--hermit-jdk-symlinks-sha256", required=True)
    parser.add_argument("--hermit-jdk-symlink-count", type=int, required=True)
    parser.add_argument("--hermit-runtime-count", type=int, required=True)
    parser.add_argument("--hermit-runtime-stream-sha256", required=True)
    parser.add_argument("--hermit-build-receipt", type=Path, required=True)
    parser.add_argument("--hermit-build-receipt-sha256", required=True)
    parser.add_argument("--hermit-build-driver", type=Path, required=True)
    parser.add_argument("--hermit-build-driver-sha256", required=True)
    parser.add_argument("--core-root", type=Path, required=True)
    parser.add_argument("--result-dir", type=Path, required=True)
    parser.add_argument(
        "--binary-override",
        type=Path,
        required=True,
        help="replay the documented route configuration with this current binary",
    )
    parser.add_argument("--binary-override-sha256", required=True)
    parser.add_argument("--source-manifest-sha256", required=True)
    parser.add_argument("--build-receipt", type=Path, required=True)
    parser.add_argument("--build-receipt-sha256", required=True)
    parser.add_argument("--km-runtime-count", type=int, required=True)
    parser.add_argument("--km-runtime-stream-sha256", required=True)
    parser.add_argument(
        "--dump-tinput",
        type=Path,
        help=(
            "optional new absolute path for the exact cb_to_ht TInput; "
            "its existence, JSON syntax, size, and hash become acceptance checks"
        ),
    )
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument(
        "--reference-timeout",
        type=float,
        default=0.0,
        help=(
            "optional larger oracle-only timeout; KM always uses --timeout"
        ),
    )
    parser.add_argument("--memcap-mb", type=int, default=20480)
    parser.add_argument(
        "--reference-memcap-mb",
        type=int,
        default=0,
        help="optional larger cap for an oracle run; KM always uses --memcap-mb",
    )
    return parser.parse_args()


def read_row(
    registry: Path, index: int, expected_count: int = 592
) -> tuple[dict[str, str], int]:
    with registry.open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    if expected_count <= 0:
        raise ValueError("expected registry row count must be positive")
    if len(rows) != expected_count:
        raise ValueError(
            f"registry must contain {expected_count} rows, found {len(rows)}"
        )
    if index < 0 or index >= len(rows):
        raise IndexError(f"row index {index} is outside 0..{len(rows) - 1}")
    return rows[index], len(rows)


def route_environment(text: str) -> list[str]:
    values = shlex.split(text)
    seen: set[str] = set()
    for value in values:
        if "=" not in value:
            raise ValueError(f"route environment token lacks '=': {value!r}")
        key, _ = value.split("=", 1)
        if not key.startswith("KM_"):
            raise ValueError(f"route environment contains non-KM key: {key!r}")
        if key in seen:
            raise ValueError(f"route environment repeats key: {key!r}")
        seen.add(key)
    return values


def verify_current_route_environment(values: list[str]) -> None:
    """Require all KM workers to come from the pinned multi-call binary."""
    forbidden = []
    for value in values:
        key, _ = value.split("=", 1)
        if key in EXTERNAL_WORKER_KEYS or key.endswith("_BIN"):
            forbidden.append(key)
    if forbidden:
        raise ValueError(
            "current route contains external worker executable overrides: "
            f"{sorted(set(forbidden))}"
        )


def binary_from_locator(locator: str) -> Path:
    prefix = "ibex:"
    if not locator.startswith(prefix):
        raise ValueError(f"unsupported binary locator: {locator!r}")
    path = Path(locator[len(prefix) :])
    if not path.is_absolute():
        raise ValueError(f"binary locator is not absolute: {locator!r}")
    return path


def verify_build_receipt(
    path: Path | None,
    expected_receipt_sha256: str,
    expected_binary_sha256: str,
    expected_source_manifest_sha256: str,
) -> tuple[str, dict]:
    """Verify that a current executable came from two identical pinned builds."""
    if path is None or not expected_receipt_sha256:
        raise ValueError(
            "a current binary requires --build-receipt and "
            "--build-receipt-sha256"
        )
    if not path.is_file():
        raise FileNotFoundError(path)
    actual_receipt_sha256 = sha256_file(path)
    if actual_receipt_sha256 != expected_receipt_sha256:
        raise ValueError(
            "build receipt hash mismatch: expected "
            f"{expected_receipt_sha256}, observed {actual_receipt_sha256}"
        )
    receipt = load_json(path)
    source = receipt.get("source") or {}
    outputs = receipt.get("outputs") or {}
    toolchain = receipt.get("toolchain") or {}
    tool_hashes = {
        toolchain.get("rustc_sha256"),
        toolchain.get("cargo_sha256"),
        toolchain.get("rustup_sha256"),
    }
    checks = {
        "receipt_status": receipt.get("status") == "verified_reproducible",
        "two_builds_byte_identical": outputs.get("byte_identical") is True,
        "receipt_binary_hash": outputs.get("binary_sha256")
        == expected_binary_sha256,
        "receipt_first_build_hash": outputs.get("build_a_sha256")
        == expected_binary_sha256,
        "receipt_second_build_hash": outputs.get("build_b_sha256")
        == expected_binary_sha256,
        "receipt_source_manifest_hash": source.get("manifest_sha256")
        == expected_source_manifest_sha256,
        "locked_dependencies": receipt.get("build", {}).get("cargo_locked") is True,
        "offline_vendored_dependencies": receipt.get("build", {}).get(
            "offline_vendored"
        )
        is True,
        "pinned_container_digest": str(
            receipt.get("container", {}).get("image_digest", "")
        ).startswith("sha256:"),
        "resolved_rustc": bool(toolchain.get("rustc_path"))
        and bool(toolchain.get("rustc_sha256")),
        "resolved_cargo": bool(toolchain.get("cargo_path"))
        and bool(toolchain.get("cargo_sha256")),
        "pinned_rustup_dispatcher": bool(toolchain.get("rustup_path"))
        and bool(toolchain.get("rustup_sha256")),
        "distinct_resolved_tool_hashes": None not in tool_hashes
        and len(tool_hashes) == 3,
    }
    failed = [name for name, value in checks.items() if not value]
    if failed:
        raise ValueError(f"build receipt failed checks: {failed}")
    return actual_receipt_sha256, receipt


def verify_konclude_build_receipt(
    *,
    receipt_path: Path,
    expected_receipt_sha256: str,
    driver: Path,
    expected_driver_sha256: str,
    binary: Path,
    expected_binary_sha256: str,
    expected_source_manifest_sha256: str,
    library_dir: Path,
    expected_runtime_manifest_sha256: str,
    expected_runtime_count: int,
) -> tuple[dict, dict[str, bool]]:
    """Verify the twice-built official Konclude source capsule."""
    if not receipt_path.is_file():
        raise FileNotFoundError(receipt_path)
    if not driver.is_file():
        raise FileNotFoundError(driver)
    receipt = load_json(receipt_path)
    source = receipt.get("source") or {}
    build = receipt.get("build") or {}
    outputs = receipt.get("outputs") or {}
    runtime = receipt.get("runtime") or {}
    artifacts = receipt.get("artifacts") or {}
    driver_sha256 = sha256_file(driver)
    checks = {
        "receipt_schema": receipt.get("schema_version") == 2,
        "receipt_sha256": sha256_file(receipt_path)
        == expected_receipt_sha256,
        "receipt_status": receipt.get("status") == "verified_reproducible",
        "official_repository": source.get("repository")
        == "https://github.com/konclude/Konclude.git",
        "official_commit": source.get("commit")
        == "0002e80635403960a7df5d93bd0e8f994d4952d0",
        "official_tag": source.get("tag") == "v0.7.0-1138",
        "official_source_archive": source.get("archive_sha256")
        == "936b65796da3209eed83d90264614067bd7d8f03133d089a64dd8bea9618076f",
        "official_source_epoch": source.get("source_date_epoch")
        == 1624053538,
        "source_manifest_sha256": source.get("manifest_sha256")
        == expected_source_manifest_sha256,
        "source_manifest_file_count": source.get("manifest_file_count")
        == 5525,
        "source_manifest_artifact": artifacts.get("source-files.sha256")
        == expected_source_manifest_sha256,
        "without_redland_project": build.get("project")
        == "KoncludeWithoutRedland.pro",
        "pinned_ibex_qt_module": build.get("module")
        == "qt/5.15.5/gnu-12.2.0",
        "qt_build_rpath_disabled": build.get("qmake_command")
        == [
            "qmake",
            "-o",
            "Makefile",
            "KoncludeWithoutRedland.pro",
            "CONFIG+=no_qt_rpath",
            "QMAKE_CXXFLAGS_RELEASE+=-ffile-prefix-map=SOURCE_TREE=.",
            "QMAKE_CXXFLAGS_RELEASE+=-fmacro-prefix-map=SOURCE_TREE=.",
            "QMAKE_LFLAGS+=-Wl,--build-id=sha1",
        ],
        "two_fresh_sequential_trees": build.get("sequential_fresh_trees")
        is True,
        "four_build_jobs": build.get("jobs") == 4,
        "no_build_network": build.get("network_used") is False,
        "site_link_rpath_cleared": build.get("ld_run_path_cleared") is True,
        "slurm_source_build": int(build.get("slurm_job_id", 0)) > 0,
        "two_builds_byte_identical": outputs.get("byte_identical") is True,
        "first_build_name": outputs.get("build_a") == "Konclude-build-a",
        "second_build_name": outputs.get("build_b") == "Konclude-build-b",
        "first_build_sha256": outputs.get("build_a_sha256")
        == expected_binary_sha256,
        "second_build_sha256": outputs.get("build_b_sha256")
        == expected_binary_sha256,
        "first_build_artifact": artifacts.get("Konclude-build-a")
        == expected_binary_sha256,
        "second_build_artifact": artifacts.get("Konclude-build-b")
        == expected_binary_sha256,
        "executed_binary_sha256": sha256_file(binary)
        == expected_binary_sha256,
        "receipt_runtime_directory": Path(
            str(runtime.get("library_directory", ""))
        )
        == library_dir,
        "receipt_runtime_manifest": runtime.get("manifest_sha256")
        == expected_runtime_manifest_sha256,
        "receipt_runtime_count": runtime.get("manifest_file_count")
        == expected_runtime_count,
        "runtime_manifest_artifact": artifacts.get("runtime-files.sha256")
        == expected_runtime_manifest_sha256,
        "driver_sha256": driver_sha256 == expected_driver_sha256,
        "receipt_binds_driver": receipt.get("driver_sha256")
        == expected_driver_sha256,
        "driver_artifact": artifacts.get(driver.name)
        == expected_driver_sha256,
    }
    if not all(checks.values()):
        failed = [name for name, passed in checks.items() if not passed]
        raise ValueError(f"Konclude build receipt failed checks: {failed}")
    return receipt, checks


def selected_routes_from_stderr(path: Path) -> list[str]:
    """Return every route trace after reading the complete stderr log."""
    routes: list[str] = []
    try:
        with path.open(encoding="utf-8", errors="replace") as handle:
            for line in handle:
                match = re.search(
                    r"KM_TIMING frontend done[^\n]* route=([a-z0-9_]+)", line
                )
                if match:
                    routes.append(match.group(1))
    except OSError:
        pass
    return routes


def selected_route_from_stderr(path: Path) -> str:
    """Return the route only when the trace contains exactly one route."""
    routes = selected_routes_from_stderr(path)
    return routes[0] if len(routes) == 1 else ""


def run_retained(
    *,
    runner: Path,
    kind: str,
    label: str,
    ontology: Path,
    binary: Path,
    output_dir: Path,
    timeout: float,
    memcap_mb: int,
    environment: list[str] = (),
    workers: int = 1,
    java: Path | None = None,
    classpath: str = "",
) -> tuple[int, str, str, dict | None]:
    command = [
        sys.executable,
        "-I",
        str(runner),
        "--kind",
        kind,
        "--label",
        label,
        "--ontology",
        str(ontology),
        "--binary",
        str(binary),
        "--output-dir",
        str(output_dir),
        "--timeout",
        str(timeout),
        "--memcap-mb",
        str(memcap_mb),
        "--workers",
        str(workers),
    ]
    if java is not None:
        command.extend(("--java", str(java)))
    if classpath:
        command.extend(("--classpath", classpath))
    for value in environment:
        command.extend(("--env", value))
    completed = subprocess.run(command, text=True, capture_output=True, check=False)
    run_path = output_dir / "run.json"
    run = load_json(run_path) if run_path.is_file() else None
    launcher_path = output_dir / "launcher.json"
    launcher = load_json(launcher_path) if launcher_path.is_file() else None
    if run is not None:
        run["launcher"] = launcher
    return completed.returncode, completed.stdout, completed.stderr, run


def run_fingerprint(
    *,
    script: Path,
    primary_output: Path,
    output_format: str,
    source_ontology: Path,
    output_prefix: Path,
) -> tuple[int, str, str, dict | None]:
    command = [
        sys.executable,
        "-I",
        str(script),
        "--input",
        str(primary_output),
        "--format",
        output_format,
        "--source-ontology",
        str(source_ontology),
        "--output-prefix",
        str(output_prefix),
    ]
    completed = subprocess.run(command, text=True, capture_output=True, check=False)
    result_path = Path(str(output_prefix) + ".json")
    result = load_json(result_path) if result_path.is_file() else None
    return completed.returncode, completed.stdout, completed.stderr, result


def run_checks(
    run: dict | None,
    expected_binary: str,
    timeout: float,
    memcap: int,
    expected_runner_sha256: str = "",
    expected_command: list[str] | None = None,
):
    if run is None:
        return {
            "run_record_exists": False,
            "status_ok": False,
            "return_code_zero": False,
            "binary_hash": False,
            "within_time": False,
            "within_memory": False,
            "sixteen_cpus": False,
            "closed_launcher_verified": False,
            "closed_launcher_environment": False,
            "closed_launcher_hash": False,
            "closed_launcher_working_directory": False,
            "exact_command": False,
        }
    launcher = run.get("launcher") or {}
    launcher_environment = launcher.get("environment") or {}
    closed_launcher_environment = (
        launcher_environment.get("PATH") == "/usr/bin:/bin"
        and launcher_environment.get("LC_ALL") == "C"
        and launcher_environment.get("PYTHONHASHSEED") == "0"
        and "LD_LIBRARY_PATH" not in launcher_environment
        and not any(key.startswith("KM_") for key in launcher_environment)
    )
    return {
        "run_record_exists": True,
        "status_ok": run.get("status") == "ok",
        "return_code_zero": run.get("return_code") == 0,
        "binary_hash": run.get("binary_sha256") == expected_binary,
        "within_time": float(run.get("wall_s", timeout + 1)) <= timeout + 0.5,
        "within_memory": float(run.get("peak_mb", memcap + 1)) <= memcap,
        "sixteen_cpus": int(run.get("cpus", 0)) == 16,
        "closed_launcher_verified": launcher.get("status") == "verified"
        and all((launcher.get("checks") or {}).values()),
        "closed_launcher_environment": closed_launcher_environment,
        "closed_launcher_hash": not expected_runner_sha256
        or launcher.get("wrapper_sha256") == expected_runner_sha256,
        "closed_launcher_working_directory": launcher.get("working_directory")
        == "/",
        "exact_command": expected_command is None
        or run.get("command") == expected_command,
    }


def fingerprint_checks(result: dict | None) -> dict[str, bool]:
    return {
        "fingerprint_record_exists": result is not None,
        "fingerprint_status_ok": result is not None and result.get("status") == "ok",
    }


def preserve_fingerprint_artifacts(
    result: dict | None,
    *,
    result_dir: Path,
    ontology: str,
    label: str,
) -> None:
    """Keep the compact per-class proof material after scratch cleanup."""
    if result is None or result.get("status") != "ok":
        return
    destination = result_dir / "fingerprints" / ontology
    destination.mkdir(parents=True, exist_ok=True)
    for path_key, hash_key, suffix in (
        ("node_fingerprints", "node_fingerprints_sha256", "nodes.tsv.gz"),
        ("unsatisfiable_names", "unsatisfiable_names_sha256", "unsat.txt.gz"),
    ):
        source_text = result.get(path_key)
        expected = result.get(hash_key)
        if not source_text or not expected:
            raise ValueError(f"fingerprint lacks {path_key}/{hash_key}")
        source = Path(source_text)
        if not source.is_file() or sha256_file(source) != expected:
            raise ValueError(f"fingerprint artifact failed hash check: {source}")
        target = destination / f"{label}.{suffix}"
        temporary = target.with_suffix(target.suffix + f".tmp.{os.getpid()}")
        shutil.copy2(source, temporary)
        if sha256_file(temporary) != expected:
            temporary.unlink(missing_ok=True)
            raise ValueError(f"copied fingerprint artifact changed: {source}")
        temporary.replace(target)
        result[path_key] = str(target)


def semantic_checks(km: dict | None, reference: dict | None) -> dict[str, bool]:
    if km is None or reference is None:
        return {
            "same_consistency": False,
            "same_taxonomy_sha256": False,
            "same_subsumption_count": False,
            "same_unsatisfiable_count": False,
            "same_source_ontology": False,
        }
    # Once an ontology is inconsistent, every axiom follows and a named-class
    # taxonomy is not an independently meaningful result.  KM serializes that
    # state as ``consistent=false`` with no taxonomy; Konclude serializes all
    # named classes as bottom-equivalent.  Treat the two representations as
    # semantically identical when, and only when, both reasoners report
    # inconsistency.
    both_inconsistent = (
        km.get("consistent") is False and reference.get("consistent") is False
    )
    return {
        "same_consistency": km.get("consistent") == reference.get("consistent"),
        "same_taxonomy_sha256": both_inconsistent
        or km.get("taxonomy_sha256") == reference.get("taxonomy_sha256"),
        "same_subsumption_count": both_inconsistent
        or km.get("subsumptions") == reference.get("subsumptions"),
        "same_unsatisfiable_count": both_inconsistent
        or km.get("unsatisfiable") == reference.get("unsatisfiable"),
        "same_source_ontology": km.get("source_ontology_sha256")
        == reference.get("source_ontology_sha256"),
    }


def copy_failure_metadata(source: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    for path in source.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(source)
        # Preserve all compact provenance and diagnostics.  Raw classifier
        # answers can be hundreds of MB; the input hash and full-IRI node files
        # retain enough identity to reproduce a mismatch without filling NFS.
        if path.name in {"stdout.log", "taxonomy.owl"} and path.stat().st_size > 8 << 20:
            continue
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)


def main() -> int:
    args = parse_args()
    if re.fullmatch(r"[a-z0-9-]+", args.validation_protocol) is None:
        raise ValueError("--validation-protocol is not a stable protocol label")
    reference_timeout = args.reference_timeout or args.timeout
    reference_memcap_mb = args.reference_memcap_mb or args.memcap_mb
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        raise ValueError("--timeout must be a finite positive number")
    if not math.isfinite(reference_timeout) or reference_timeout < args.timeout:
        raise ValueError(
            "--reference-timeout must be zero or a finite value no smaller "
            "than --timeout"
        )
    if args.memcap_mb <= 0:
        raise ValueError("--memcap-mb must be positive")
    if reference_memcap_mb < args.memcap_mb:
        raise ValueError(
            "--reference-memcap-mb must be zero or no smaller than --memcap-mb"
        )
    validator_environment, validator_environment_status = (
        validator_environment_checks()
    )
    row, row_count = read_row(
        args.registry, args.row_index, args.expected_registry_row_count
    )
    ontology_name = row["ontology"]
    expected_ontology_sha256 = row.get("ontology_sha256", "")
    if re.fullmatch(r"[0-9a-f]{64}", expected_ontology_sha256) is None:
        raise ValueError(
            f"registry row lacks an exact ontology SHA-256: {ontology_name}"
        )
    result_path = args.result_dir / "results" / f"{ontology_name}.json"
    actual_validation_driver_sha256 = (
        sha256_file(args.validation_driver)
        if args.validation_driver.is_file()
        else ""
    )
    validation_driver_check = (
        actual_validation_driver_sha256 == args.validation_driver_sha256
    )
    record: dict = {
        "schema_version": 1,
        "validation_protocol": args.validation_protocol,
        "phase": "initialised",
        "confirmation_status": "running",
        "confirmed": False,
        "row_index": args.row_index,
        "row_count": row_count,
        "ontology": ontology_name,
        "expected_ontology_sha256": expected_ontology_sha256,
        "registry_sha256": sha256_file(args.registry),
        "validator_sha256": sha256_file(Path(__file__)),
        "runner_sha256": sha256_file(args.runner),
        "fingerprint_tool_sha256": sha256_file(args.fingerprint),
        "validation_driver": str(args.validation_driver),
        "validation_driver_sha256": actual_validation_driver_sha256,
        "validation_driver_check": validation_driver_check,
        "route_observation_policy": args.route_observation_policy,
        "documented_state": row["state"],
        "documented_route": row["route"],
        "documented_route_kind": row["route_kind"],
        "documented_binary_sha256": row["binary_sha256"],
        "documented_binary_locator": row["binary_locator"],
        "documented_source_revision": row["source_revision"],
        "documented_environment": row["route_environment"],
        "documented_signature_sha256": row["signature_sha256"],
        "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
        "slurm_array_job_id": os.environ.get("SLURM_ARRAY_JOB_ID"),
        "slurm_array_task_id": os.environ.get("SLURM_ARRAY_TASK_ID"),
        "host": os.uname().nodename,
        "km_memory_limit_mb": args.memcap_mb,
        "reference_memory_limit_mb": reference_memcap_mb,
        "reference_timeout_s": reference_timeout,
        "validator_environment": validator_environment,
        "validator_environment_checks": validator_environment_status,
    }
    atomic_json(result_path, record)

    if not all(validator_environment_status.values()):
        record.update(
            phase="complete",
            confirmation_status="validator_environment_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    if not validation_driver_check:
        record.update(
            phase="complete",
            confirmation_status="validation_driver_mismatch",
            confirmed=False,
        )
        atomic_json(result_path, record)
        return 1

    if row["state"] not in CLAIMED_STATES:
        ontology_source = args.km_root / "corpus" / ontology_name
        if not ontology_source.is_file():
            record.update(
                phase="complete",
                confirmation_status="validation_error",
                error=f"missing ontology: {ontology_source}",
                confirmed=False,
            )
            atomic_json(result_path, record)
            return 1
        ontology_source_sha256 = sha256_file(ontology_source)
        if ontology_source_sha256 != expected_ontology_sha256:
            record.update(
                phase="complete",
                confirmation_status="ontology_hash_mismatch",
                confirmed=False,
                ontology_sha256=ontology_source_sha256,
            )
            atomic_json(result_path, record)
            return 1
        record.update(
            phase="complete",
            confirmation_status="not_a_documented_solve_claim",
            confirmed=False,
            ontology_sha256=ontology_source_sha256,
        )
        atomic_json(result_path, record)
        return 0

    temporary_root = Path(
        tempfile.mkdtemp(
            prefix=f"km-route-{ontology_name}-",
            dir=os.environ.get("SLURM_TMPDIR") or None,
        )
    )
    try:
        ontology_source = args.km_root / "corpus" / ontology_name
        if not ontology_source.is_file():
            raise FileNotFoundError(ontology_source)
        ontology_source_sha256 = sha256_file(ontology_source)
        if ontology_source_sha256 != expected_ontology_sha256:
            raise ValueError(
                "ontology hash mismatch: expected "
                f"{expected_ontology_sha256}, observed {ontology_source_sha256}"
            )
        ontology = temporary_root / ontology_name
        shutil.copy2(ontology_source, ontology)
        if sha256_file(ontology) != expected_ontology_sha256:
            raise ValueError("copied ontology no longer matches the pinned bytes")

        binary = args.binary_override
        if not binary.is_file():
            raise FileNotFoundError(binary)
        actual_binary_sha = sha256_file(binary)
        expected_binary_sha = args.binary_override_sha256
        record["actual_binary_sha256"] = actual_binary_sha
        record["binary_provenance_match"] = actual_binary_sha == expected_binary_sha
        record["executed_binary"] = str(binary)
        record["executed_binary_sha256"] = expected_binary_sha
        record["executed_source_manifest_sha256"] = args.source_manifest_sha256
        if actual_binary_sha != expected_binary_sha:
            raise ValueError(
                f"binary hash mismatch: expected {expected_binary_sha}, "
                f"observed {actual_binary_sha}"
            )
        receipt_sha, receipt = verify_build_receipt(
            args.build_receipt,
            args.build_receipt_sha256,
            expected_binary_sha,
            args.source_manifest_sha256,
        )
        km_runtime = executable_runtime_identity(
            binary=binary,
            environment={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            expected_ldd_sha256=args.ldd_sha256,
        )
        km_runtime_checks = {
            "binary_sha256": km_runtime.get("binary_sha256")
            == expected_binary_sha,
            "ldd_sha256": km_runtime.get("ldd_sha256") == args.ldd_sha256,
            "runtime_library_count": km_runtime.get("runtime_library_count")
            == args.km_runtime_count,
            "runtime_library_manifest_sha256": km_runtime.get(
                "runtime_library_manifest_sha256"
            )
            == args.km_runtime_stream_sha256,
        }
        if not all(km_runtime_checks.values()):
            raise ValueError(
                "KM runtime closure failed checks: "
                f"{[key for key, passed in km_runtime_checks.items() if not passed]}"
            )
        record.update(
            executed_build_receipt=str(args.build_receipt),
            executed_build_receipt_sha256=receipt_sha,
            build_receipt=receipt,
            km_runtime=km_runtime,
            km_runtime_checks=km_runtime_checks,
        )
        environment = route_environment(row["route_environment"])
        if not any(value.startswith("KM_ROUTE=") for value in environment):
            # Several historical witnesses predate automatic routing. Their
            # explicit KM_* flags were the route. Current KM defaults to
            # `auto`, so `manual` is required to reproduce that exact bundle
            # instead of letting the new decision tree replace it.
            environment.insert(0, "KM_ROUTE=manual")
        verify_current_route_environment(environment)
        effective_route_request = next(
            (
                value.split("=", 1)[1]
                for value in environment
                if value.startswith("KM_ROUTE=")
            ),
            "",
        )
        dump_tinput = args.dump_tinput
        if dump_tinput is not None:
            if not dump_tinput.is_absolute():
                raise ValueError("--dump-tinput must be an absolute path")
            if dump_tinput.exists():
                raise FileExistsError(
                    f"refusing to overwrite TInput dump: {dump_tinput}"
                )
            dump_tinput.parent.mkdir(parents=True, exist_ok=True)
        instrumentation_environment = ["KM_TIMING=1"]
        if dump_tinput is not None:
            instrumentation_environment.append(f"KM_DUMP_TIN={dump_tinput}")
        executed_environment = environment + instrumentation_environment
        instrumentation_specification = {
            value.split("=", 1)[0]: value.split("=", 1)[1]
            for value in instrumentation_environment
        }
        ontology_sha256 = sha256_file(ontology)
        semantic_environment = dict(
            sorted(value.split("=", 1) for value in environment)
        )
        semantic_environment_sha256 = canonical_json_sha256(
            semantic_environment
        )
        current_route_label = effective_route_request
        if effective_route_request == "manual":
            current_route_label = (
                f"manual@sha256:{semantic_environment_sha256}"
            )
        route_specification = {
            "schema_version": 2,
            "binary_sha256": expected_binary_sha,
            "source_manifest_sha256": args.source_manifest_sha256,
            "build_receipt_sha256": receipt_sha,
            "runtime_library_manifest_sha256": (
                args.km_runtime_stream_sha256
            ),
            "runtime_library_count": args.km_runtime_count,
            "ontology_sha256": ontology_sha256,
            "command": [str(binary), "classify", str(ontology)],
            "semantic_environment": semantic_environment,
            "instrumentation_environment": instrumentation_specification,
            "closed_base_environment": {
                "PATH": "/usr/bin:/bin",
                "LC_ALL": "C",
                "PYTHONHASHSEED": "0",
            },
            "validator_sha256": sha256_file(Path(__file__)),
            "runner_wrapper_sha256": sha256_file(args.runner),
            "fingerprint_tool_sha256": sha256_file(args.fingerprint),
            "validation_driver_sha256": actual_validation_driver_sha256,
            "route_observation_policy": args.route_observation_policy,
            "cpus": 16,
            "timeout_s": args.timeout,
            "memory_limit_mb": args.memcap_mb,
        }
        record["parsed_environment"] = environment
        record["effective_route_request"] = effective_route_request
        record["current_route_label"] = current_route_label
        record["semantic_environment_sha256"] = semantic_environment_sha256
        record["instrumentation_environment"] = instrumentation_environment
        record["executed_environment"] = executed_environment
        record["route_specification"] = route_specification
        record["route_specification_sha256"] = canonical_json_sha256(
            route_specification
        )
        record["ontology_sha256"] = ontology_sha256
        record["phase"] = "provenance_verified"
        atomic_json(result_path, record)

        # Materialize the independent full-IRI reference before KM.  A route
        # timeout or mismatch must not prevent other current routes for the
        # same ontology from being compared with this fresh oracle result.
        reference_fingerprint = None
        ref_fp_rc = -1
        ref_fp_stdout = ""
        ref_fp_stderr = ""
        if row["state"] == EXACT:
            konclude_sha = sha256_file(args.konclude)
            konclude_build_receipt, konclude_build_checks = (
                verify_konclude_build_receipt(
                    receipt_path=args.konclude_build_receipt,
                    expected_receipt_sha256=(
                        args.konclude_build_receipt_sha256
                    ),
                    driver=args.konclude_build_driver,
                    expected_driver_sha256=args.konclude_build_driver_sha256,
                    binary=args.konclude,
                    expected_binary_sha256=args.konclude_sha256,
                    expected_source_manifest_sha256=(
                        args.konclude_source_manifest_sha256
                    ),
                    library_dir=args.konclude_library_dir,
                    expected_runtime_manifest_sha256=(
                        args.konclude_runtime_stream_sha256
                    ),
                    expected_runtime_count=args.konclude_runtime_count,
                )
            )
            konclude_runtime = konclude_runtime_identity(
                binary=args.konclude,
                library_dir=args.konclude_library_dir,
                expected_ldd_sha256=args.ldd_sha256,
            )
            konclude_runtime_checks = {
                "binary_sha256": konclude_sha == args.konclude_sha256,
                "runtime_binary_sha256": konclude_runtime.get("binary_sha256")
                == args.konclude_sha256,
                "ldd_sha256": konclude_runtime.get("ldd_sha256")
                == args.ldd_sha256,
                "closed_runtime_environment": konclude_runtime.get("environment")
                == {
                    "PATH": "/usr/bin:/bin",
                    "LC_ALL": "C",
                    "PYTHONHASHSEED": "0",
                    "LD_LIBRARY_PATH": str(args.konclude_library_dir),
                },
                "working_directory": konclude_runtime.get("working_directory")
                == "/",
                "runtime_library_count": konclude_runtime.get(
                    "runtime_library_count"
                )
                == args.konclude_runtime_count,
                "runtime_library_manifest_sha256": konclude_runtime.get(
                    "runtime_library_manifest_sha256"
                )
                == args.konclude_runtime_stream_sha256,
                "source_build_receipt": all(konclude_build_checks.values()),
                "no_external_sw_runtime": all(
                    not entry.get("path", "").startswith("/sw/")
                    for entry in konclude_runtime.get(
                        "runtime_libraries", []
                    )
                ),
            }
            if not all(konclude_runtime_checks.values()):
                raise ValueError(
                    "Konclude runtime closure failed checks: "
                    f"{[key for key, passed in konclude_runtime_checks.items() if not passed]}"
                )
            reference_memcap_mb = args.reference_memcap_mb or args.memcap_mb
            reference_timeout = args.reference_timeout or args.timeout
            reference_dir = temporary_root / "konclude"
            reference_command = [
                str(args.konclude),
                "classification",
                "-w",
                "16",
                "-v",
                "-i",
                str(ontology),
                "-o",
                str(reference_dir / "taxonomy.owl"),
            ]
            reference_route_specification = {
                "schema_version": 1,
                "command": reference_command,
                "binary_sha256": args.konclude_sha256,
                "ontology_sha256": ontology_sha256,
                "working_directory": "/",
                "environment": konclude_runtime["environment"],
                "runtime_library_manifest_sha256": konclude_runtime[
                    "runtime_library_manifest_sha256"
                ],
                "runtime_library_count": konclude_runtime[
                    "runtime_library_count"
                ],
                "build_receipt_sha256": args.konclude_build_receipt_sha256,
                "source_manifest_sha256": (
                    args.konclude_source_manifest_sha256
                ),
                "build_driver_sha256": args.konclude_build_driver_sha256,
                "runner_wrapper_sha256": sha256_file(args.runner),
                "fingerprint_tool_sha256": sha256_file(args.fingerprint),
                "cpus": 16,
                "timeout_s": reference_timeout,
                "memory_limit_mb": reference_memcap_mb,
            }
            ref_rc, ref_stdout, ref_stderr, reference_run = run_retained(
                runner=args.runner,
                kind="konclude",
                label=f"fresh_konclude_{ontology_name}",
                ontology=ontology,
                binary=args.konclude,
                output_dir=reference_dir,
                timeout=reference_timeout,
                memcap_mb=reference_memcap_mb,
                environment=[
                    f"LD_LIBRARY_PATH={args.konclude_library_dir}"
                ],
                workers=16,
            )
            reference_checks = run_checks(
                reference_run,
                konclude_sha,
                reference_timeout,
                reference_memcap_mb,
                sha256_file(args.runner),
                reference_command,
            )
            reference_checks["explicit_runtime_environment"] = (
                (reference_run or {}).get("environment")
                == {"LD_LIBRARY_PATH": str(args.konclude_library_dir)}
            )
            record.update(
                phase="konclude_finished",
                reference_binary_sha256=konclude_sha,
                reference_build_receipt=konclude_build_receipt,
                reference_build_receipt_sha256=(
                    args.konclude_build_receipt_sha256
                ),
                reference_build_checks=konclude_build_checks,
                reference_runtime=konclude_runtime,
                reference_runtime_checks=konclude_runtime_checks,
                reference_command=reference_command,
                reference_route_specification=reference_route_specification,
                reference_route_specification_sha256=canonical_json_sha256(
                    reference_route_specification
                ),
                reference_runner_return_code=ref_rc,
                reference_runner_stdout=ref_stdout[-4000:],
                reference_runner_stderr=ref_stderr[-4000:],
                reference_run=reference_run,
                reference_checks=reference_checks,
            )
            atomic_json(result_path, record)
            if reference_run is None or reference_run.get("status") != "ok":
                raise RuntimeError(
                    f"fresh Konclude did not complete successfully: {reference_run!r}"
                )

            reference_primary = Path(reference_run["primary_output"])
            reference_prefix = temporary_root / "fingerprints" / "konclude"
            ref_fp_rc, ref_fp_stdout, ref_fp_stderr, reference_fingerprint = (
                run_fingerprint(
                    script=args.fingerprint,
                    primary_output=reference_primary,
                    output_format="owlxml",
                    source_ontology=ontology,
                    output_prefix=reference_prefix,
                )
            )
            preserve_fingerprint_artifacts(
                reference_fingerprint,
                result_dir=args.result_dir,
                ontology=ontology_name,
                label="konclude",
            )
            reference_fingerprint_checks = fingerprint_checks(
                reference_fingerprint
            )
            reference_ready = (
                ref_fp_rc == 0
                and all(reference_checks.values())
                and all(konclude_runtime_checks.values())
                and all(reference_fingerprint_checks.values())
            )
            record.update(
                phase="reference_fingerprinted",
                reference_fingerprint_return_code=ref_fp_rc,
                reference_fingerprint_stdout=ref_fp_stdout[-4000:],
                reference_fingerprint_stderr=ref_fp_stderr[-4000:],
                reference_fingerprint=reference_fingerprint,
                reference_fingerprint_checks=reference_fingerprint_checks,
                reference_ready=reference_ready,
            )
            atomic_json(result_path, record)
            if not reference_ready:
                raise RuntimeError("fresh Konclude full-IRI reference failed")

        km_dir = temporary_root / "km"
        km_rc, km_stdout, km_stderr, km_run = run_retained(
            runner=args.runner,
            kind="km",
            label=f"documented_{row['route']}_{ontology_name}",
            ontology=ontology,
            binary=binary,
            output_dir=km_dir,
            timeout=args.timeout,
            memcap_mb=args.memcap_mb,
            environment=executed_environment,
            workers=16,
        )
        km_checks = run_checks(
            km_run,
            expected_binary_sha,
            args.timeout,
            args.memcap_mb,
            sha256_file(args.runner),
            [str(binary), "classify", str(ontology)],
        )
        selected_route_traces = selected_routes_from_stderr(
            km_dir / "stderr.log"
        )
        selected_route = (
            selected_route_traces[0]
            if len(selected_route_traces) == 1
            else ""
        )
        run_environment = (km_run or {}).get("environment") or {}
        expected_run_environment = dict(
            value.split("=", 1) for value in executed_environment
        )
        complete_execution_environment = run_environment == expected_run_environment
        if args.route_observation_policy == "runtime-trace":
            trace_count_valid = len(selected_route_traces) == 1
            route_observation_valid = selected_route == effective_route_request
            route_observation_kind = "runtime_trace"
            observed_route_identity = selected_route
        else:
            trace_count_valid = len(selected_route_traces) <= 1
            trace_compatible = not selected_route_traces or (
                selected_route == effective_route_request
            )
            route_observation_valid = (
                effective_route_request == "manual"
                and current_route_label.startswith("manual@sha256:")
                and complete_execution_environment
                and trace_compatible
            )
            route_observation_kind = (
                "runtime_trace_and_closed_semantic_environment"
                if selected_route_traces
                else "closed_semantic_environment"
            )
            observed_route_identity = current_route_label
        km_checks.update(
            {
                "effective_route_request_recorded": run_environment.get("KM_ROUTE")
                == effective_route_request,
                "timing_instrumentation_recorded": run_environment.get("KM_TIMING")
                == "1",
                "complete_execution_environment": complete_execution_environment,
                "route_trace_count_valid_for_policy": trace_count_valid,
                "route_observation_policy_satisfied": route_observation_valid,
                "validation_driver_hash": validation_driver_check,
                **{
                    f"validator_environment_{key}": value
                    for key, value in validator_environment_status.items()
                },
            }
        )
        tinput_dump_record = None
        if dump_tinput is not None:
            tinput_is_file = dump_tinput.is_file()
            tinput_size = dump_tinput.stat().st_size if tinput_is_file else 0
            tinput_json_object = False
            tinput_top_level_keys: list[str] = []
            if tinput_is_file and tinput_size > 0:
                try:
                    tinput_value = load_json(dump_tinput)
                    tinput_json_object = isinstance(tinput_value, dict)
                    if tinput_json_object:
                        tinput_top_level_keys = sorted(tinput_value)
                except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                    pass
            tinput_dump_record = {
                "path": str(dump_tinput),
                "bytes": tinput_size,
                "sha256": sha256_file(dump_tinput) if tinput_is_file else "",
                "top_level_keys": tinput_top_level_keys,
            }
            km_checks.update(
                {
                    "tinput_dump_exists": tinput_is_file,
                    "tinput_dump_nonempty": tinput_size > 0,
                    "tinput_dump_json_object": tinput_json_object,
                }
            )
        km_checks.update(
            {
                f"runtime_{key}": value
                for key, value in km_runtime_checks.items()
            }
        )
        record.update(
            phase="km_finished",
            km_runner_return_code=km_rc,
            km_runner_stdout=km_stdout[-4000:],
            km_runner_stderr=km_stderr[-4000:],
            km_run=km_run,
            selected_route_trace=selected_route,
            selected_route_traces=selected_route_traces,
            selected_route_trace_count=len(selected_route_traces),
            route_observation_kind=route_observation_kind,
            observed_route_identity=observed_route_identity,
            tinput_dump=tinput_dump_record,
            km_checks=km_checks,
        )
        atomic_json(result_path, record)
        if km_run is None or km_run.get("status") != "ok":
            record.update(
                phase="complete",
                confirmation_status="km_limit_or_execution_failure",
                confirmed=False,
                checks=km_checks,
            )
            atomic_json(result_path, record)
            copy_failure_metadata(
                temporary_root, args.result_dir / "failures" / ontology_name
            )
            return 1

        km_primary = Path(km_run["primary_output"])
        km_prefix = temporary_root / "fingerprints" / "km"
        km_fp_rc, km_fp_stdout, km_fp_stderr, km_fingerprint = run_fingerprint(
            script=args.fingerprint,
            primary_output=km_primary,
            output_format="json",
            source_ontology=ontology,
            output_prefix=km_prefix,
        )
        preserve_fingerprint_artifacts(
            km_fingerprint,
            result_dir=args.result_dir,
            ontology=ontology_name,
            label="km",
        )
        record.update(
            phase="km_fingerprinted",
            km_fingerprint_return_code=km_fp_rc,
            km_fingerprint_stdout=km_fp_stdout[-4000:],
            km_fingerprint_stderr=km_fp_stderr[-4000:],
            km_fingerprint=km_fingerprint,
            km_fingerprint_checks=fingerprint_checks(km_fingerprint),
        )
        atomic_json(result_path, record)
        if km_fingerprint is None or km_fp_rc != 0:
            record.update(
                phase="complete",
                confirmation_status="km_full_iri_fingerprint_failed",
                confirmed=False,
            )
            atomic_json(result_path, record)
            copy_failure_metadata(
                temporary_root, args.result_dir / "failures" / ontology_name
            )
            return 1

        if row["state"] == EXACT:
            checks = {}
            checks.update(record["km_checks"])
            checks.update(
                {f"reference_{key}": value for key, value in record["reference_checks"].items()}
            )
            checks.update(
                {
                    f"reference_runtime_{key}": value
                    for key, value in record["reference_runtime_checks"].items()
                }
            )
            checks.update(record["km_fingerprint_checks"])
            checks.update(
                {
                    f"reference_{key}": value
                    for key, value in fingerprint_checks(reference_fingerprint).items()
                }
            )
            checks.update(semantic_checks(km_fingerprint, reference_fingerprint))
            confirmed = all(checks.values()) and ref_fp_rc == 0
            record.update(
                phase="complete",
                checks=checks,
                confirmed=confirmed,
                confirmation_status=(
                    "confirmed_exact_full_iri"
                    if confirmed
                    else "full_iri_mismatch_or_limit_failure"
                ),
            )
        else:
            hermit_build_receipt, hermit_build_checks = (
                verify_hermit_build_receipt(
                    receipt_path=args.hermit_build_receipt,
                    expected_receipt_sha256=args.hermit_build_receipt_sha256,
                    driver=args.hermit_build_driver,
                    expected_driver_sha256=args.hermit_build_driver_sha256,
                    oracle=args.hermit_oracle,
                    expected_oracle_sha256=args.hermit_oracle_sha256,
                    source=args.hermit_source,
                    expected_source_sha256=args.hermit_source_sha256,
                    java=args.hermit_java,
                    expected_java_sha256=args.hermit_java_sha256,
                    expected_javac_sha256=args.hermit_javac_sha256,
                    classpath=args.hermit_classpath,
                    classpath_manifest=args.hermit_classpath_manifest,
                    expected_classpath_manifest_sha256=(
                        args.hermit_classpath_manifest_sha256
                    ),
                    expected_classpath_count=args.hermit_classpath_count,
                    jdk_manifest=args.hermit_jdk_manifest,
                    expected_jdk_manifest_sha256=args.hermit_jdk_manifest_sha256,
                    expected_jdk_count=args.hermit_jdk_count,
                    jdk_symlinks=args.hermit_jdk_symlinks,
                    expected_jdk_symlinks_sha256=(
                        args.hermit_jdk_symlinks_sha256
                    ),
                    expected_jdk_symlink_count=args.hermit_jdk_symlink_count,
                )
            )
            hermit_runtime = executable_runtime_identity(
                binary=args.hermit_java,
                environment={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
                expected_ldd_sha256=args.ldd_sha256,
            )
            hermit_runtime_checks = {
                "java_binary_sha256": hermit_runtime.get("binary_sha256")
                == args.hermit_java_sha256,
                "ldd_sha256": hermit_runtime.get("ldd_sha256")
                == args.ldd_sha256,
                "runtime_library_count": hermit_runtime.get(
                    "runtime_library_count"
                )
                == args.hermit_runtime_count,
                "runtime_library_manifest_sha256": hermit_runtime.get(
                    "runtime_library_manifest_sha256"
                )
                == args.hermit_runtime_stream_sha256,
            }
            failed_hermit_provenance = [
                name
                for name, passed in {
                    **{
                        f"build_{key}": value
                        for key, value in hermit_build_checks.items()
                    },
                    **{
                        f"runtime_{key}": value
                        for key, value in hermit_runtime_checks.items()
                    },
                }.items()
                if not passed
            ]
            if failed_hermit_provenance:
                raise ValueError(
                    "HermiT oracle provenance failed checks: "
                    f"{failed_hermit_provenance}"
                )
            hermit_dir = temporary_root / "hermit-full"
            hermit_command = [
                str(args.hermit_java),
                "-Xmx16g",
                "-cp",
                args.hermit_classpath,
                "Oracle",
                str(ontology),
            ]
            hermit_route_specification = {
                "schema_version": 1,
                "command": hermit_command,
                "ontology_sha256": ontology_sha256,
                "oracle_binary_sha256": args.hermit_oracle_sha256,
                "oracle_source_sha256": args.hermit_source_sha256,
                "oracle_build_receipt_sha256": (
                    args.hermit_build_receipt_sha256
                ),
                "java_sha256": args.hermit_java_sha256,
                "jdk_manifest_sha256": args.hermit_jdk_manifest_sha256,
                "jdk_symlinks_sha256": args.hermit_jdk_symlinks_sha256,
                "classpath_manifest_sha256": (
                    args.hermit_classpath_manifest_sha256
                ),
                "runtime_library_manifest_sha256": (
                    args.hermit_runtime_stream_sha256
                ),
                "closed_base_environment": {
                    "PATH": "/usr/bin:/bin",
                    "LC_ALL": "C",
                    "PYTHONHASHSEED": "0",
                },
                "working_directory": "/",
                "cpus": 16,
                "reasoner_workers": 1,
                "timeout_s": reference_timeout,
                "memory_limit_mb": reference_memcap_mb,
            }
            hermit_rc, hermit_stdout, hermit_stderr, hermit_run = run_retained(
                runner=args.runner,
                kind="hermit",
                label=f"fresh_hermit_full_{ontology_name}",
                ontology=ontology,
                binary=args.hermit_oracle,
                output_dir=hermit_dir,
                timeout=reference_timeout,
                memcap_mb=reference_memcap_mb,
                workers=1,
                java=args.hermit_java,
                classpath=args.hermit_classpath,
            )
            hermit_prefix = temporary_root / "fingerprints" / "hermit-full"
            hermit_fingerprint = None
            hermit_fp_rc = -1
            hermit_fp_stdout = ""
            hermit_fp_stderr = ""
            if hermit_run is not None and hermit_run.get("status") == "ok":
                (
                    hermit_fp_rc,
                    hermit_fp_stdout,
                    hermit_fp_stderr,
                    hermit_fingerprint,
                ) = run_fingerprint(
                    script=args.fingerprint,
                    primary_output=Path(hermit_run["primary_output"]),
                    output_format="json",
                    source_ontology=ontology,
                    output_prefix=hermit_prefix,
                )
                preserve_fingerprint_artifacts(
                    hermit_fingerprint,
                    result_dir=args.result_dir,
                    ontology=ontology_name,
                    label="hermit-full",
                )
            hermit_sha = sha256_file(args.hermit_oracle)
            hermit_run_checks = run_checks(
                hermit_run,
                args.hermit_oracle_sha256,
                reference_timeout,
                reference_memcap_mb,
                sha256_file(args.runner),
                hermit_command,
            )
            checks = {}
            checks.update(record["km_checks"])
            checks.update(record["km_fingerprint_checks"])
            checks.update(
                {
                    f"hermit_{key}": value
                    for key, value in hermit_run_checks.items()
                }
            )
            checks.update(
                {
                    f"hermit_build_{key}": value
                    for key, value in hermit_build_checks.items()
                }
            )
            checks.update(
                {
                    f"hermit_runtime_{key}": value
                    for key, value in hermit_runtime_checks.items()
                }
            )
            checks.update(
                {
                    "km_reports_inconsistent": km_fingerprint.get("consistent") is False,
                    "hermit_full_ontology_hash": hermit_run is not None
                    and hermit_run.get("ontology_sha256")
                    == expected_ontology_sha256,
                    "hermit_full_status_ok": hermit_run is not None
                    and hermit_run.get("status") == "ok",
                    "hermit_full_return_code_zero": hermit_run is not None
                    and hermit_run.get("return_code") == 0,
                    "hermit_oracle_hash": hermit_run is not None
                    and hermit_run.get("binary_sha256")
                    == args.hermit_oracle_sha256,
                    "hermit_java_hash": hermit_run is not None
                    and hermit_run.get("runtime_sha256")
                    == args.hermit_java_sha256,
                    "hermit_fingerprint_status_ok": hermit_fingerprint is not None
                    and hermit_fingerprint.get("status") == "ok",
                    "hermit_full_reports_inconsistent": hermit_fingerprint is not None
                    and hermit_fingerprint.get("consistent") is False,
                }
            )
            confirmed = all(checks.values()) and hermit_rc == 0 and hermit_fp_rc == 0
            record.update(
                phase="complete",
                hermit_ontology=str(ontology_source),
                hermit_ontology_sha256=ontology_sha256,
                hermit_oracle_sha256=hermit_sha,
                hermit_java_sha256=args.hermit_java_sha256,
                hermit_build_receipt_sha256=args.hermit_build_receipt_sha256,
                hermit_classpath_manifest_sha256=(
                    args.hermit_classpath_manifest_sha256
                ),
                hermit_jdk_manifest_sha256=args.hermit_jdk_manifest_sha256,
                hermit_jdk_symlinks_sha256=args.hermit_jdk_symlinks_sha256,
                hermit_runtime_stream_sha256=args.hermit_runtime_stream_sha256,
                hermit_build_receipt=hermit_build_receipt,
                hermit_build_checks=hermit_build_checks,
                hermit_runtime=hermit_runtime,
                hermit_runtime_checks=hermit_runtime_checks,
                hermit_command=hermit_command,
                hermit_route_specification=hermit_route_specification,
                hermit_route_specification_sha256=canonical_json_sha256(
                    hermit_route_specification
                ),
                hermit_run_checks=hermit_run_checks,
                hermit_runner_return_code=hermit_rc,
                hermit_runner_stdout=hermit_stdout[-4000:],
                hermit_runner_stderr=hermit_stderr[-4000:],
                hermit_run=hermit_run,
                hermit_fingerprint_return_code=hermit_fp_rc,
                hermit_fingerprint_stdout=hermit_fp_stdout[-4000:],
                hermit_fingerprint_stderr=hermit_fp_stderr[-4000:],
                hermit_fingerprint=hermit_fingerprint,
                checks=checks,
                confirmed=confirmed,
                confirmation_status=(
                    "confirmed_adjudicated_inconsistent"
                    if confirmed
                    else "adjudicated_inconsistency_check_failed"
                ),
            )

        atomic_json(result_path, record)
        if not record["confirmed"]:
            copy_failure_metadata(
                temporary_root, args.result_dir / "failures" / ontology_name
            )
        return 0 if record["confirmed"] else 1
    except Exception as error:  # noqa: BLE001 - every task needs a terminal row
        record.update(
            phase="complete",
            confirmation_status="validation_error",
            confirmed=False,
            error=repr(error),
            traceback=traceback.format_exc()[-12000:],
        )
        atomic_json(result_path, record)
        copy_failure_metadata(
            temporary_root, args.result_dir / "failures" / ontology_name
        )
        return 1
    finally:
        shutil.rmtree(temporary_root, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
