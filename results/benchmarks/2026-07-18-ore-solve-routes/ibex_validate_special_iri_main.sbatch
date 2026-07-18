#!/bin/bash
# Direct full-IRI regression of the release candidate built from latest source.
#SBATCH --job-name=km-iri-main-val
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-3%4
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/special-iri-main-20260718/slurm/validate-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
run_root=$km_root/routing_20260715/special-iri-main-20260718
source_root=$run_root/source
tools=$source_root/results/benchmarks/2026-07-18-ore-solve-routes
binary=$run_root/target/release/km
runner=$tools/validate_tail_runner.py
fingerprint=$tools/fingerprint_tail_fulliri.py
told_validator=$tools/validate_told_subclass_target.py
corpus=$km_root/corpus

case ${SLURM_ARRAY_TASK_ID:-0} in
    0)
        ontology_id=3524
        expected_taxonomy=090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a
        expected_pairs=1604386
        expected_unsat=0
        ;;
    1)
        ontology_id=15703
        expected_taxonomy=090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a
        expected_pairs=1604386
        expected_unsat=0
        ;;
    2)
        ontology_id=13503
        expected_taxonomy=1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b
        expected_pairs=113
        expected_unsat=1
        ;;
    3)
        ontology_id=7581
        expected_taxonomy=27a29aab966ffea74df4aa09c0520545f5908c9fc8e3fc5d10cd3e027b9118d4
        expected_pairs=1246911
        expected_unsat=0
        ;;
    *) exit 2 ;;
esac

ontology=$corpus/ore_ont_${ontology_id}.owl
label=km_special_iri_main_${ontology_id}
out=$run_root/results/$label
/usr/bin/mkdir -p "$out" "$run_root/slurm"

/usr/bin/python3 "$runner" \
    --kind km --label "$label" --ontology "$ontology" --binary "$binary" \
    --output-dir "$out" --timeout 240 --memcap-mb 20480 \
    --env KM_ROUTE=production_all

/usr/bin/timeout -k 10 900 /usr/bin/python3 "$fingerprint" \
    --input "$out/stdout.log" --format json --source-ontology "$ontology" \
    --output-prefix "$out/fulliri-source"

if [[ "$ontology_id" == 3524 || "$ontology_id" == 15703 ]]; then
    target='http://purl.obolibrary.org/obo/BFO_0000050_some_http://www.w3.org/2002/07/owl#Thing'
    /usr/bin/python3 "$told_validator" \
        --ontology "$ontology" --km-output "$out/stdout.log" --target "$target" \
        --output "$out/told-target-validation.json" --ignore-reflexive
fi

/usr/bin/python3 - \
    "$out/fulliri-source.json" "$expected_taxonomy" "$expected_pairs" \
    "$expected_unsat" "$ontology_id" "$out/direct-verdict.json" <<'PY'
import json
from pathlib import Path
import sys

fingerprint = json.loads(Path(sys.argv[1]).read_text())
expected_taxonomy = sys.argv[2]
expected_pairs = int(sys.argv[3])
expected_unsat = int(sys.argv[4])
ontology_id = int(sys.argv[5])
verdict_path = Path(sys.argv[6])
checks = {
    "status_ok": fingerprint.get("status") == "ok",
    "consistent": fingerprint.get("consistent") is True,
    "taxonomy_sha256": fingerprint.get("taxonomy_sha256") == expected_taxonomy,
    "subsumptions": fingerprint.get("subsumptions") == expected_pairs,
    "unsatisfiable": fingerprint.get("unsatisfiable") == expected_unsat,
}
record = {
    "schema_version": 1,
    "ontology_id": ontology_id,
    "expected_taxonomy_sha256": expected_taxonomy,
    "observed_taxonomy_sha256": fingerprint.get("taxonomy_sha256"),
    "expected_subsumptions": expected_pairs,
    "observed_subsumptions": fingerprint.get("subsumptions"),
    "expected_unsatisfiable": expected_unsat,
    "observed_unsatisfiable": fingerprint.get("unsatisfiable"),
    "checks": checks,
    "verdict": "match" if all(checks.values()) else "mismatch",
}
verdict_path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
print(json.dumps(record, sort_keys=True))
if record["verdict"] != "match":
    raise SystemExit(1)
PY

/usr/bin/printf 'VALIDATED ontology=%s host=%s binary=%s\n' \
    "$ontology_id" "$(hostname)" "$binary"
