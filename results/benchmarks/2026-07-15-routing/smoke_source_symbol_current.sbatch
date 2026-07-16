#!/bin/bash
# Exact closure gate for source IRIs whose local names look like KM-generated
# symbols, followed by the nominal closure regressions from ORE 148.
#SBATCH --job-name=km-source-symbol-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/source-symbol-smoke-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=${SMOKE_RUNNER:-$root/bench_one_matrix_current.py}
km=${SMOKE_KM:-$root/km-source-symbol-current}
result=${SMOKE_RESULT:-$root/source-symbol-smoke-${SLURM_JOB_ID}.jsonl}
failure_dir=${SMOKE_FAILURE_DIR:-$root/failures-source-symbol-current}
work=${SLURM_TMPDIR:-/tmp}/km-source-symbol-smoke-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$failure_dir" "$root/slurm"
: > "$result"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
position=0
for ont_id in 8864 12009 6817 148 178 11016; do
  ontology=ore_ont_${ont_id}.owl
  local_ontology=$work/$ontology
  route=cb_plain16
  if [[ $ont_id == 148 || $ont_id == 178 || $ont_id == 11016 ]]; then
    route=nominals
  fi
  /usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
  /usr/bin/python3 "$runner" \
    --kind km --arm "$route" --ontology "$local_ontology" \
    --binary "$km" --binary-sha "$km_sha" \
    --gold "$km_root/gold/konclude__$ontology.sig.gz" --gold-kind konclude \
    --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$position" --timeout 240 --memcap-mb 20480 \
    --env "KM_ROUTE=$route" >> "$result"
  position=$((position + 1))
done

/usr/bin/python3 - "$result" "$km_sha" <<'PY'
import json
import sys

rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
expected = {
    "ore_ont_8864.owl": "cb_plain16",
    "ore_ont_12009.owl": "cb_plain16",
    "ore_ont_6817.owl": "cb_plain16",
    "ore_ont_148.owl": "nominals",
    "ore_ont_178.owl": "nominals",
    "ore_ont_11016.owl": "nominals",
}
assert len(rows) == len(expected), rows
assert {row["ont"] for row in rows} == set(expected), rows
for row in rows:
    assert row["arm"] == expected[row["ont"]], row
    assert row["binary_sha256"] == sys.argv[2], row
    assert row["status"] == "ok", row
    assert row["verdict"] == "match", row
    assert row["extra"] == row["missing"] == 0, row
    assert row["extra_unsat"] == row["missing_unsat"] == 0, row
    assert not row["consistency_mismatch"], row
print(json.dumps(rows, indent=2, sort_keys=True))
PY

/usr/bin/rm -rf "$work"
