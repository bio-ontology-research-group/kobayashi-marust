#!/bin/bash
# Representative route proof before the 592-ontology launch.
#SBATCH --job-name=km-proof-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:45:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-5%6
#SBATCH --output=/ibex/scratch/hohndor/km/route_proof_20260716/slurm/smoke-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
proof_root=$km_root/route_proof_20260716
matrix_root=$km_root/routing_20260715
runner=$matrix_root/bench_one_matrix-3b1d2a87.py
km=$proof_root/km
gold_dir=$km_root/gold
result_dir=$proof_root/smoke-results
failure_dir=$proof_root/smoke-failures
work=${SLURM_TMPDIR:-/tmp}/km-proof-smoke-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

# Easy EL, ordinary CB, nominal, cardinality, KPSet bridge, and rule-clash cases.
onts=(33 105 10702 7499 3215 2669)
routes=(elc cb_plain16 nominals production_all production_all ht_rules)
ontology=ore_ont_${onts[${SLURM_ARRAY_TASK_ID}]}.owl
route=${routes[${SLURM_ARRAY_TASK_ID}]}
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
result=$result_dir/${route}__${ontology}.jsonl

mkdir -p "$result_dir" "$failure_dir" "$work"
cp "$km_root/corpus/$ontology" "$local_ontology"
"$km" routes | grep -q '^production_all'
km_sha=$(sha256sum "$km" | cut -d' ' -f1)

python3 "$runner" \
  --kind km --arm "$route" --ontology "$local_ontology" \
  --binary "$km" --binary-sha "$km_sha" \
  --gold "$gold_dir/konclude__$ontology.sig.gz" --gold-kind konclude \
  --workdir "$work" --failures-dir "$failure_dir" \
  --timeout 240 --memcap-mb 20480 --env "KM_ROUTE=$route" > "$result"

python3 - "$result" "$ontology" "$route" "$km_sha" <<'PY'
import json
import sys

path, ontology, route, binary_sha = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    row = json.load(handle)
if row["ont"] != ontology or row["arm"] != route:
    raise SystemExit("smoke provenance mismatch")
if row["binary_sha256"] != binary_sha:
    raise SystemExit("smoke binary hash mismatch")
if row["status"] != "ok" or row["verdict"] != "match":
    raise SystemExit(
        f"smoke failed: {ontology} {route} {row['status']} {row['verdict']}"
    )
if not row.get("signature_sha256") or row.get("wall_s", 0) <= 0:
    raise SystemExit("smoke lacks real signature or runtime")
PY

rm -rf "$work" "$local_ontology"
printf 'SMOKE_OK ontology=%s route=%s\n' "$ontology" "$route"
