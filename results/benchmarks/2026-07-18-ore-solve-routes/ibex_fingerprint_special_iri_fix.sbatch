#!/bin/bash
# Low-memory full-IRI adjudication of the completed 3524/15703 fix runs.
# The classification outputs and run metadata come from job 49086707.
#SBATCH --job-name=km-iri-fingerprint
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=8G
#SBATCH --array=0-1%2
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/special-iri-fix-20260718/slurm/fingerprint-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
run_root=$km_root/routing_20260715/special-iri-fix-20260718
fingerprint=$run_root/tools/fingerprint_tail_fulliri.py
told_validator=$run_root/tools/validate_told_subclass_target.py
expected_taxonomy=090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a
expected_binary=2db2491a93c07f90803f4dcbf6cc2b2d2434996fb8f8daa6a4387031042025e1

case ${SLURM_ARRAY_TASK_ID:-0} in
    0) ontology_id=3524 ;;
    1) ontology_id=15703 ;;
    *) exit 2 ;;
esac

ontology=$km_root/corpus/ore_ont_${ontology_id}.owl
out=$run_root/results/km_special_iri_fix_${ontology_id}

# Refuse to adjudicate a stale, failed or differently built classification.
/usr/bin/python3 - "$out/run.json" "$expected_binary" "$ontology_id" <<'PY'
import json
from pathlib import Path
import sys

record = json.loads(Path(sys.argv[1]).read_text())
expected_binary = sys.argv[2]
ontology_id = sys.argv[3]
checks = [
    record.get("status") == "ok",
    record.get("return_code") == 0,
    record.get("binary_sha256") == expected_binary,
    record.get("ontology", "").endswith(f"ore_ont_{ontology_id}.owl"),
    Path(record.get("primary_output", "")).is_file(),
]
if not all(checks):
    raise SystemExit("classification provenance check failed")
PY

/usr/bin/timeout -k 10 900 /usr/bin/python3 "$fingerprint" \
    --input "$out/stdout.log" --format json --source-ontology "$ontology" \
    --output-prefix "$out/fulliri-source"

target='http://purl.obolibrary.org/obo/BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing'
/usr/bin/python3 "$told_validator" \
    --ontology "$ontology" --km-output "$out/stdout.log" --target "$target" \
    --output "$out/told-target-validation.json" --ignore-reflexive

/usr/bin/python3 - "$out/fulliri-source.json" "$expected_taxonomy" \
    "$ontology_id" "$out/direct-verdict.json" <<'PY'
import json
from pathlib import Path
import sys

fingerprint = json.loads(Path(sys.argv[1]).read_text())
expected_taxonomy = sys.argv[2]
ontology_id = int(sys.argv[3])
verdict_path = Path(sys.argv[4])
checks = {
    "status_ok": fingerprint.get("status") == "ok",
    "consistent": fingerprint.get("consistent") is True,
    "taxonomy_sha256": fingerprint.get("taxonomy_sha256") == expected_taxonomy,
    "subsumptions": fingerprint.get("subsumptions") == 1_604_386,
    "unsatisfiable": fingerprint.get("unsatisfiable") == 0,
}
record = {
    "schema_version": 1,
    "ontology_id": ontology_id,
    "expected_taxonomy_sha256": expected_taxonomy,
    "observed_taxonomy_sha256": fingerprint.get("taxonomy_sha256"),
    "expected_subsumptions": 1_604_386,
    "observed_subsumptions": fingerprint.get("subsumptions"),
    "expected_unsatisfiable": 0,
    "observed_unsatisfiable": fingerprint.get("unsatisfiable"),
    "checks": checks,
    "verdict": "match" if all(checks.values()) else "mismatch",
}
temporary = verdict_path.with_suffix(verdict_path.suffix + ".tmp")
temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
temporary.replace(verdict_path)
print(json.dumps(record, sort_keys=True))
if record["verdict"] != "match":
    raise SystemExit(1)
PY

/usr/bin/printf 'FINGERPRINT_VALIDATED ontology=%s host=%s\n' \
    "$ontology_id" "$(hostname)"
