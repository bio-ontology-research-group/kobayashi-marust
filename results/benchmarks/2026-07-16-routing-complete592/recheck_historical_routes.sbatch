#!/bin/bash
# Focused restoration check for routes with retained historical exact evidence.
#SBATCH --job-name=km-restore-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-29%16
#SBATCH --output=/ibex/scratch/hohndor/km/route_proof_20260716/slurm/restore-%A_%a.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
proof_root=$km_root/route_proof_20260716
runner=$km_root/routing_20260715/bench_one_matrix-3b1d2a87.py
km=$proof_root/km
gold_dir=$km_root/gold
result_dir=$proof_root/restoration-results
failure_dir=$proof_root/restoration-failures
work=${SLURM_TMPDIR:-/tmp}/km-restore-${SLURM_JOB_ID}_${SLURM_ARRAY_TASK_ID}

cases=(
  10702:auto 10702:default 10702:nominals 10702:ht_full
  10908:ht_general 10908:ht_shoq 10908:ht_full
  11745:auto 11745:cb_plain16
  15672:ht_shoq 15672:ht_general 15672:ht_full
  6934:ht_general 6934:ht_full
  7499:ht_card 7499:card_fn 7499:production_all
  9540:ht_card 9540:card_fn 9540:production_all
  9635:tableau 9635:tab_race 9635:ht_bridge
  3215:ht_bridge 3215:production_all
  2669:ht_rules 15516:ht_rules
  10702:production_all 15672:production_all 6934:production_all
)

entry=${cases[${SLURM_ARRAY_TASK_ID}]}
id=${entry%%:*}
route=${entry#*:}
ontology=ore_ont_${id}.owl
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
  --workdir "$work" --failures-dir "$failure_dir/$route" \
  --timeout 240 --memcap-mb 20480 --env "KM_ROUTE=$route" > "$result"

python3 - "$result" "$ontology" "$route" "$km_sha" <<'PY'
import json
import sys

path, ontology, route, binary_sha = sys.argv[1:]
with open(path, encoding="utf-8") as handle:
    row = json.load(handle)
if row.get("ont") != ontology or row.get("arm") != route:
    raise SystemExit("restoration provenance mismatch")
if row.get("binary_sha256") != binary_sha:
    raise SystemExit("restoration binary hash mismatch")
if row.get("status") == "error":
    raise SystemExit(f"restoration execution error: {ontology} {route}")
PY

rm -rf "$work" "$local_ontology"
printf 'RESTORE_RESULT ontology=%s route=%s\n' "$ontology" "$route"
