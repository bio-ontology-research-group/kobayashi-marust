#!/usr/bin/env python3
"""Run the frozen 68-procedure panel for one ORE ontology."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from full_panel_contract import panel

try:
    import full_panel_correctness as _correctness
except ModuleNotFoundError:
    # The repository keeps the reusable scorer one directory above this dated
    # benchmark.  Frozen IBEX deployments place the same hash-pinned module
    # beside the driver.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
    import full_panel_correctness as _correctness

classify_correctness = _correctness.classify_correctness
CORRECTNESS_SCORER_PATH = Path(_correctness.__file__).resolve()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def combined_manifest(paths: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in sorted((path.resolve(strict=True) for path in paths), key=str):
        encoded = str(path).encode("utf-8")
        digest.update(len(encoded).to_bytes(8, "big"))
        digest.update(encoded)
        digest.update(bytes.fromhex(sha256_file(path)))
    return digest.hexdigest()


def read_json_line(stdout: str) -> dict | None:
    for line in reversed(stdout.splitlines()):
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            return value
    return None


def validate_existing(path: Path, expected_ontology: str, expected_arms: list[str]) -> bool:
    if not path.is_file():
        return False
    try:
        rows = [json.loads(line) for line in path.read_text().splitlines() if line]
    except (OSError, json.JSONDecodeError):
        return False
    return (
        len(rows) == len(expected_arms)
        and [row.get("arm") for row in rows] == expected_arms
        and all(row.get("ont") == expected_ontology for row in rows)
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--task-index", type=int, required=True)
    parser.add_argument("--ontology-list", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--gold", type=Path, required=True)
    parser.add_argument("--build-root", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path, required=True)
    parser.add_argument("--result-root", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--fingerprint", type=Path, required=True)
    parser.add_argument("--rustdl-adapter", type=Path, required=True)
    parser.add_argument("--sequoia-adapter", type=Path, required=True)
    parser.add_argument("--konclude", type=Path, required=True)
    parser.add_argument("--konclude-library", type=Path, required=True)
    parser.add_argument("--konclude-runtime-manifest", type=Path, required=True)
    parser.add_argument("--elk", type=Path, required=True)
    parser.add_argument("--hermit-oracle", type=Path, required=True)
    parser.add_argument("--hermit-classpath", required=True)
    parser.add_argument("--java", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=240.0)
    parser.add_argument("--memcap-mb", type=int, default=20480)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    procedures = panel()
    expected_arms = [row["arm"] for row in procedures]
    ontologies = [line.strip() for line in args.ontology_list.read_text().splitlines() if line.strip()]
    if len(ontologies) != 592:
        raise SystemExit(f"expected 592 ontologies, found {len(ontologies)}")
    if not 0 <= args.task_index < len(ontologies):
        raise SystemExit(f"task index out of range: {args.task_index}")
    ontology = ontologies[args.task_index]
    if not ontology.startswith("ore_ont_") or not ontology.endswith(".owl"):
        raise SystemExit(f"invalid ontology name: {ontology!r}")

    result_path = args.result_root / "results" / f"{ontology}.jsonl"
    if validate_existing(result_path, ontology, expected_arms):
        print(f"SKIP complete ontology={ontology}", flush=True)
        return 0

    source = args.corpus / ontology
    if not source.is_file():
        raise SystemExit(f"missing ontology: {source}")
    job_id = os.environ.get("SLURM_JOB_ID", "local")
    workdir = args.work_root / f"task-{job_id}-{args.task_index}-{os.getpid()}"
    if workdir.exists():
        raise SystemExit(f"refusing pre-existing work directory: {workdir}")
    workdir.mkdir(parents=True)
    local_ontology = workdir / ontology
    shutil.copy2(source, local_ontology)

    args.result_root.joinpath("results").mkdir(parents=True, exist_ok=True)
    args.result_root.joinpath("failures", ontology).mkdir(parents=True, exist_ok=True)
    fingerprint_dir = args.result_root / "fingerprints" / ontology
    fingerprint_dir.mkdir(parents=True, exist_ok=True)

    build_receipt = args.build_root / "build-receipt.json"
    if not build_receipt.is_file():
        raise SystemExit(f"missing build receipt: {build_receipt}")
    build_receipt_sha = sha256_file(build_receipt)
    rustdl = args.build_root / "bin" / "rustdl"
    sequoia = (args.build_root / "bin" / "sequoia").resolve(strict=True)
    sequoia_manifest = args.build_root / "sequoia-files.sha256"
    for required in (
        args.runner,
        args.fingerprint,
        args.rustdl_adapter,
        args.sequoia_adapter,
        args.konclude,
        args.konclude_runtime_manifest,
        args.elk,
        args.hermit_oracle,
        args.java,
        rustdl,
        sequoia,
        sequoia_manifest,
    ):
        if not required.is_file():
            raise SystemExit(f"missing benchmark input: {required}")
    if not args.konclude_library.is_dir():
        raise SystemExit(f"missing Konclude runtime library directory: {args.konclude_library}")

    binary_shas: dict[Path, str] = {}

    def sha(path: Path) -> str:
        resolved = path.resolve(strict=True)
        if resolved not in binary_shas:
            binary_shas[resolved] = sha256_file(resolved)
        return binary_shas[resolved]

    hermit_jars = sorted(Path(args.benchmark_root / "hermit_cp").glob("*.jar"))
    if not hermit_jars:
        raise SystemExit(f"no HermiT runtime jars under {args.benchmark_root / 'hermit_cp'}")
    hermit_runtime_sha = combined_manifest([args.java, args.hermit_oracle, *hermit_jars])
    sequoia_runtime_sha = combined_manifest([args.java, sequoia_manifest])
    konclude_runtime_sha = sha256_file(args.konclude_runtime_manifest)
    java_sha = sha(args.java)
    gold_path = args.gold / f"konclude__{ontology}.sig.gz"
    has_gold = gold_path.is_file()
    source_sha = sha256_file(source)

    # Rotate execution order by ontology to distribute cache/order effects.  The
    # final file is restored to contract order; order_index records execution.
    offset = args.task_index % len(procedures)
    execution = procedures[offset:] + procedures[:offset]
    rows_by_arm: dict[str, dict] = {}

    for order_index, procedure in enumerate(execution):
        arm = procedure["arm"]
        arm_work = workdir / arm
        arm_work.mkdir()
        checkpoint = arm_work / "checkpoint.jsonl"
        kind = procedure["kind"]
        runtime_sha = ""
        runner_kind = kind
        environment: list[str] = []
        runner_extra: list[str] = []
        underlying_command: list[str] | None = None

        if kind == "km":
            binary = args.build_root / "bin" / f"km-{procedure['binary_key']}"
            if procedure["family"] == "km_documented_solution_route":
                environment.extend(procedure["environment"])
            else:
                environment.append(f"KM_ROUTE={procedure['route']}")
        elif kind == "konclude":
            binary = args.konclude
            runtime_sha = konclude_runtime_sha
            runner_extra.extend(
                ["--workers", "16", "--library-path", str(args.konclude_library)]
            )
        elif kind == "elk":
            binary = args.elk
            runtime_sha = java_sha
            runner_extra.extend(["--java", str(args.java), "--java-heap=-Xmx16g"])
        elif kind == "hermit":
            binary = args.hermit_oracle
            runtime_sha = hermit_runtime_sha
            runner_extra.extend(
                [
                    "--java",
                    str(args.java),
                    "--java-heap=-Xmx16g",
                    "--classpath",
                    args.hermit_classpath,
                    "--hermit-main-class",
                    "FullIriHermitOracle",
                ]
            )
        elif kind == "rustdl":
            runner_kind = "km"
            binary = args.rustdl_adapter
            runtime_sha = sha(rustdl)
            environment.extend(
                [
                    f"RUSTDL_BINARY={rustdl}",
                    f"RUSTDL_MODE={'default' if arm == 'rustdl_default' else 'complete'}",
                ]
            )
            underlying_command = [
                str(rustdl),
                "classify",
                str(local_ontology),
                *procedure.get("args", []),
            ]
        elif kind == "sequoia":
            runner_kind = "km"
            binary = args.sequoia_adapter
            runtime_sha = sequoia_runtime_sha
            environment.extend(
                [
                    f"SEQUOIA_BINARY={sequoia}",
                    "SEQUOIA_MODE=ignore_unsupported"
                    if arm == "sequoia_ignore_unsupported"
                    else "SEQUOIA_MODE=strict",
                ]
            )
            underlying_command = [
                str(sequoia),
                "-main",
                "com.sequoiareasoner.cli.Sequoia",
                "classify",
                *procedure.get("args", []),
                "--output",
                "<adapter-temporary-taxonomy>",
                str(local_ontology),
            ]
        else:
            raise AssertionError(kind)
        if not binary.is_file():
            raise SystemExit(f"missing binary for {arm}: {binary}")

        command = [
            "/usr/bin/python3",
            str(args.runner),
            "--kind",
            runner_kind,
            "--arm",
            arm,
            "--ontology",
            str(local_ontology),
            "--binary",
            str(binary),
            "--binary-sha",
            sha(binary),
            "--workdir",
            str(arm_work),
            "--failures-dir",
            str(args.result_root / "failures" / ontology),
            "--checkpoint",
            str(checkpoint),
            "--order-index",
            str(order_index),
            "--timeout",
            str(args.timeout),
            "--memcap-mb",
            str(args.memcap_mb),
            "--retain-output",
            *runner_extra,
        ]
        if runtime_sha:
            command.extend(["--runtime-sha", runtime_sha])
        if has_gold:
            command.extend(["--gold", str(gold_path), "--gold-kind", "konclude"])
        else:
            command.extend(["--gold-kind", "none"])
        for item in environment:
            command.extend(["--env", item])

        completed = subprocess.run(command, text=True, capture_output=True, check=False)
        row = read_json_line(completed.stdout)
        if row is None and checkpoint.is_file():
            row = read_json_line(checkpoint.read_text(encoding="utf-8", errors="replace"))
        if row is None:
            row = {
                "ont": ontology,
                "arm": arm,
                "status": "harness_error",
                "verdict": "harness_error",
                "rc": completed.returncode,
                "binary_sha256": sha(binary),
                "err_tail": (completed.stderr or completed.stdout)[-1000:],
            }

        row.update(
            family=procedure["family"],
            procedure_kind=kind,
            procedure_contract=procedure,
            source_ontology_sha256=source_sha,
            build_receipt_sha256=build_receipt_sha,
            benchmark_driver_sha256=sha256_file(Path(__file__)),
            correctness_scorer_sha256=sha256_file(CORRECTNESS_SCORER_PATH),
            fingerprint_driver_sha256=sha(args.fingerprint),
            contract_sha256=sha256_file(Path(__file__).with_name("full_panel_contract.py")),
            fulliri_identity_capable=True,
            underlying_command=underlying_command,
            limit_timeout_s=args.timeout,
            limit_memcap_mib=args.memcap_mb,
            rss_sample_interval_ms=20,
        )
        row.setdefault("runner_sha256", sha(args.runner))
        output = Path(row["output_path"]) if row.get("output_path") else None
        if row.get("status") == "ok" and output and output.is_file():
            prefix = fingerprint_dir / arm
            fingerprint_command = [
                "/usr/bin/python3",
                str(args.fingerprint),
                "--input",
                str(output),
                "--format",
                row.get("output_format", "json"),
                "--output-prefix",
                str(prefix),
            ]
            try:
                fingerprint_run = subprocess.run(
                    fingerprint_command,
                    text=True,
                    capture_output=True,
                    timeout=1800,
                    check=False,
                )
            except subprocess.TimeoutExpired:
                fingerprint_run = None
            fingerprint_json = Path(str(prefix) + ".json")
            if fingerprint_run and fingerprint_run.returncode == 0 and fingerprint_json.is_file():
                fingerprint = json.loads(fingerprint_json.read_text())
                row.update(
                    fulliri_fingerprint_status="ok",
                    fulliri_taxonomy_sha256=fingerprint["taxonomy_sha256"],
                    fulliri_subsumptions=fingerprint["subsumptions"],
                    fulliri_unsatisfiable=fingerprint["unsatisfiable"],
                    fulliri_fingerprint_json=str(fingerprint_json),
                    fulliri_fingerprint_json_sha256=sha256_file(fingerprint_json),
                    fulliri_nodes_sha256=fingerprint["node_fingerprints_sha256"],
                    fulliri_unsat_sha256=fingerprint["unsatisfiable_names_sha256"],
                )
                row["consistent"] = fingerprint["consistent"]
            else:
                row["fulliri_fingerprint_status"] = (
                    "timeout" if fingerprint_run is None else "error"
                )
                row["fulliri_fingerprint_error"] = (
                    "postprocess timeout"
                    if fingerprint_run is None
                    else (fingerprint_run.stderr or fingerprint_run.stdout)[-1000:]
                )
        else:
            row["fulliri_fingerprint_status"] = "not_applicable"
        if output and output.is_file():
            output.unlink()
        rows_by_arm[arm] = row
        print(
            f"DONE ontology={ontology} arm={arm} status={row.get('status')} "
            f"wall={row.get('wall_s')} peak={row.get('peak_mb')}",
            flush=True,
        )

    reference = rows_by_arm.get("konclude")
    rows = [rows_by_arm[arm] for arm in expected_arms]
    for row in rows:
        classify_correctness(row, reference)

    temporary_result = result_path.with_suffix(result_path.suffix + f".tmp.{os.getpid()}")
    with temporary_result.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    temporary_result.replace(result_path)
    shutil.rmtree(workdir)
    print(f"PANEL_COMPLETE ontology={ontology} rows={len(rows)} result={result_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
