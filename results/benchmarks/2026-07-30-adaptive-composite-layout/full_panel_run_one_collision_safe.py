#!/usr/bin/env python3
"""Adjudicate ORE cases whose local-name signature is not semantics-preserving."""

import json
import os
from pathlib import Path
import subprocess
import sys


EXPECTED = {
    "ore_ont_3524.owl": "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a",
    # A legal source class ends in #Nothing. The ORE local-name projection
    # mistakes it for owl:Nothing and reports a false extra-unsatisfiable row.
    "ore_ont_13503.owl": "1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b",
    # The same full-IRI SCC fingerprint over the independently adjudicated
    # private-mirror taxonomy. Its separate pair-stream oracle digest is d02d…;
    # the two encodings both cover 846,306 pairs and zero UNSAT names.
    "ore_ont_4669.owl": "a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30",
    "ore_ont_15703.owl": "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a",
}
HERE = Path(__file__).resolve().parent
RUNNER = HERE / "full_panel_run_one_fulliri_only.py"
FINGERPRINT = HERE / "full_panel_fingerprint.py"


def option(name):
    try:
        index = sys.argv.index(name)
    except ValueError:
        return None
    return sys.argv[index + 1] if index + 1 < len(sys.argv) else None


def atomic_row(path, row):
    if not path:
        return
    target = Path(path)
    temporary = target.with_name(f"{target.name}.collision-safe.{os.getpid()}")
    with temporary.open("w", encoding="utf-8") as handle:
        handle.write(json.dumps(row, sort_keys=True) + "\n")
        handle.flush()
        os.fsync(handle.fileno())
    temporary.replace(target)


def parse_last_row(text):
    for line in reversed(text.splitlines()):
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(row, dict):
            return row
    raise ValueError("full-IRI runner emitted no terminal JSON row")


def main():
    ontology_path = option("--ontology")
    ontology = Path(ontology_path).name if ontology_path else ""
    if ontology not in EXPECTED:
        raise SystemExit(
            f"collision-safe runner is restricted to {sorted(EXPECTED)}, "
            f"received {ontology!r}"
        )

    command = ["/usr/bin/python3", str(RUNNER), *sys.argv[1:]]
    if "--retain-output" not in command:
        command.append("--retain-output")
    run = subprocess.run(command, text=True, capture_output=True, check=False)
    row = parse_last_row(run.stdout)
    output = Path(row["output_path"]) if row.get("output_path") else None

    if row.get("status") == "ok" and output and output.is_file():
        prefix = Path(option("--workdir")) / "fulliri-fingerprint"
        fingerprint_run = subprocess.run(
            [
                "/usr/bin/python3",
                str(FINGERPRINT),
                "--input",
                str(output),
                "--format",
                "json",
                "--source-ontology",
                ontology_path,
                "--output-prefix",
                str(prefix),
            ],
            text=True,
            capture_output=True,
            timeout=1800,
            check=False,
        )
        fingerprint_path = Path(str(prefix) + ".json")
        if fingerprint_run.returncode == 0 and fingerprint_path.is_file():
            fingerprint = json.loads(fingerprint_path.read_text(encoding="utf-8"))
            digest = fingerprint.get("taxonomy_sha256")
            exact = digest == EXPECTED[ontology]
            correctness_basis = (
                "same_job_fulliri_identity_to_independent_mirror_oracle"
                if ontology == "ore_ont_4669.owl"
                else "same_job_fulliri_identity_to_konclude"
            )
            row.update(
                fulliri_fingerprint_status="ok",
                fulliri_taxonomy_sha256=digest,
                fulliri_subsumptions=fingerprint.get("subsumptions"),
                fulliri_unsatisfiable=fingerprint.get("unsatisfiable"),
                fulliri_fingerprint_wall_s=fingerprint.get("wall_s"),
                fulliri_fingerprint_peak_mb=fingerprint.get("peak_mb"),
                fulliri_identity_capable=True,
                correctness_basis=correctness_basis,
                verdict="match" if exact else "both",
                solved=exact,
                signature_sha256=digest,
            )
        else:
            row.update(
                status="output_error",
                verdict="fulliri_fingerprint_error",
                solved=False,
                fulliri_fingerprint_status="error",
                fulliri_fingerprint_error=(
                    fingerprint_run.stderr or fingerprint_run.stdout
                )[-1000:],
            )
    elif row.get("status") == "ok":
        row.update(
            status="output_error",
            verdict="missing_retained_output",
            solved=False,
            fulliri_fingerprint_status="error",
        )

    if output:
        try:
            output.unlink()
        except OSError:
            pass
    row["output_path"] = None
    atomic_row(option("--checkpoint"), row)
    print(json.dumps(row, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
