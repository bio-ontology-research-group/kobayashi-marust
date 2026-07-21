#!/usr/bin/env python3
"""Launch the retained one-reasoner runner under a closed environment.

The retained runner is useful evidence code, but it inherited the submitting
shell and silently supplied Konclude's private library directory.  This small
source-bound launcher makes that behaviour reproducible without rewriting the
historical helper: it verifies the exact helper and runtime tools, records the
environment it will expose, then replaces itself with the helper.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import sys


INNER_RUNNER_SHA256 = (
    "8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4"
)
PYTHON_SHA256 = (
    "aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1"
)
GNU_TIME_SHA256 = (
    "db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6"
)
PYTHON = Path("/usr/bin/python3")
GNU_TIME = Path("/usr/bin/time")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def option_path(arguments: list[str], option: str) -> Path:
    try:
        index = arguments.index(option)
        value = arguments[index + 1]
    except (ValueError, IndexError) as error:
        raise SystemExit(f"missing launcher option {option}") from error
    return Path(value)


def atomic_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + f".tmp.{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def main() -> int:
    arguments = sys.argv[1:]
    output_dir = option_path(arguments, "--output-dir")
    inner_runner = Path(__file__).resolve().with_name("validate_tail_runner.py")
    python_resolved = PYTHON.resolve(strict=True)
    time_resolved = GNU_TIME.resolve(strict=True)
    checks = {
        "inner_runner": inner_runner.is_file()
        and sha256_file(inner_runner) == INNER_RUNNER_SHA256,
        "python": sha256_file(python_resolved) == PYTHON_SHA256,
        "gnu_time": sha256_file(time_resolved) == GNU_TIME_SHA256,
    }
    if not all(checks.values()):
        atomic_json(
            output_dir / "launcher.json",
            {
                "schema_version": 1,
                "status": "mismatch",
                "checks": checks,
            },
        )
        return 2

    # Only variables required by the retained runner's accounting survive.
    # Every semantic KM setting is supplied later through explicit --env
    # arguments, including the exact source-built Konclude library directory.
    # The retained runner must not invent a historical private-library path.
    environment = {
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "PYTHONHASHSEED": "0",
    }
    for key in (
        "SLURM_ARRAY_JOB_ID",
        "SLURM_ARRAY_TASK_ID",
        "SLURM_CPUS_PER_TASK",
        "SLURM_JOB_ID",
    ):
        if key in os.environ:
            environment[key] = os.environ[key]
    if os.environ.get("SLURM_TMPDIR"):
        environment["SLURM_TMPDIR"] = os.environ["SLURM_TMPDIR"]
        environment["TMPDIR"] = os.environ["SLURM_TMPDIR"]

    command = [str(PYTHON), str(inner_runner), *arguments]
    working_directory = "/"
    atomic_json(
        output_dir / "launcher.json",
        {
            "schema_version": 1,
            "status": "verified",
            "checks": checks,
            "wrapper": str(Path(__file__).resolve()),
            "wrapper_sha256": sha256_file(Path(__file__).resolve()),
            "inner_runner": str(inner_runner),
            "inner_runner_sha256": INNER_RUNNER_SHA256,
            "python": str(PYTHON),
            "python_resolved": str(python_resolved),
            "python_sha256": PYTHON_SHA256,
            "gnu_time": str(GNU_TIME),
            "gnu_time_resolved": str(time_resolved),
            "gnu_time_sha256": GNU_TIME_SHA256,
            "environment": environment,
            "working_directory": working_directory,
            "command": command,
            "acceptance_evidence": False,
        },
    )
    os.chdir(working_directory)
    os.execve(str(PYTHON), command, environment)
    raise AssertionError("execve returned")


if __name__ == "__main__":
    raise SystemExit(main())
