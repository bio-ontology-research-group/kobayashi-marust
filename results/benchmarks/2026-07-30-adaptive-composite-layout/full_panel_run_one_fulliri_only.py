#!/usr/bin/env python3
"""Run one panel arm while deferring unsafe local-name scoring.

ORE ontologies 3524 and 15703 have non-injective local-name projections.
Ontology 13503 has a legal named source class ending in ``#Nothing`` that the
legacy projection confuses with OWL bottom. Ontology 4669 emits a taxonomy too
large for the legacy projection to canonicalize within the harness cgroup. In
all four cases the full-IRI streaming path is required.

This narrowly gated wrapper keeps the frozen reasoner runner and its resource
measurement unchanged. For a successful classification it records the local
projection as inapplicable and retains the taxonomy for the exact full-IRI
fingerprinter. Its provenance records hashes for this wrapper and the base
runner.
"""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys


ALLOWED_ONTOLOGIES = {
    "ore_ont_3524.owl",
    "ore_ont_13503.owl",
    "ore_ont_4669.owl",
    "ore_ont_15703.owl",
}
BASE_RUNNER = Path(__file__).with_name("full_panel_run_one.py").resolve()
THIS_RUNNER = Path(__file__).resolve()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def option_value(name: str) -> str | None:
    try:
        index = sys.argv.index(name)
    except ValueError:
        return None
    if index + 1 >= len(sys.argv):
        return None
    return sys.argv[index + 1]


def write_checkpoint(record: dict) -> None:
    checkpoint = option_value("--checkpoint")
    if not checkpoint:
        return
    target = Path(checkpoint)
    temporary = Path(f"{target}.fulliri-only.{os.getpid()}")
    with temporary.open("w", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    temporary.replace(target)


def main() -> int:
    ontology_argument = option_value("--ontology")
    ontology = Path(ontology_argument).name if ontology_argument else ""
    if ontology not in ALLOWED_ONTOLOGIES:
        raise SystemExit(
            "full-IRI-only runner is restricted to "
            f"{sorted(ALLOWED_ONTOLOGIES)}, received {ontology!r}"
        )
    if not BASE_RUNNER.is_file():
        raise SystemExit(f"missing frozen base runner: {BASE_RUNNER}")

    specification = importlib.util.spec_from_file_location(
        "_full_panel_run_one_frozen", BASE_RUNNER
    )
    if specification is None or specification.loader is None:
        raise SystemExit(f"cannot load frozen base runner: {BASE_RUNNER}")
    base = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(base)

    wrapper_sha = sha256_file(THIS_RUNNER)
    base_sha = sha256_file(BASE_RUNNER)
    original_sha256_file = base.sha256_file

    def provenance_sha256_file(path):
        if Path(path).resolve() == BASE_RUNNER:
            return wrapper_sha
        return original_sha256_file(path)

    def defer_local_projection(_output, _output_format, _gold_path):
        return (
            "localname_not_applicable_fulliri_only",
            0,
            0,
            0,
            0,
            False,
            None,
            None,
        )

    base.sha256_file = provenance_sha256_file
    base.compare_output = defer_local_projection

    captured = io.StringIO()
    with contextlib.redirect_stdout(captured):
        base.main()
    record = None
    for line in reversed(captured.getvalue().splitlines()):
        try:
            candidate = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(candidate, dict):
            record = candidate
            break
    if record is None:
        raise SystemExit("frozen base runner did not emit a terminal JSON row")

    record["runner_sha256"] = wrapper_sha
    record["runner_base_sha256"] = base_sha
    record["localname_identity_capable"] = False
    record["localname_canonicalization_status"] = (
        "skipped_unsafe_projection"
        if record.get("status") == "ok"
        else "not_applicable_no_answer"
    )
    write_checkpoint(record)
    print(json.dumps(record, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
