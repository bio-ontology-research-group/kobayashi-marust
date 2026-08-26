#!/bin/bash
#SBATCH --job-name=km-v110-v5-top40
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-39%8
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825/top40/slurm-%A_%a.out

set -euo pipefail
ids=(3215 14817 8737 16744 10621 13482 15280 9724 1012 7499 10750 10689 9674 868 8486 1559 14459 15703 15059 6682 6233 11395 9663 14042 1306 6212 16008 15803 8480 7246 3377 3524 4205 11460 3836 12528 10073 3560 11745 11315)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v1-cert-overhead-v5-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
sha=e9f06cda45e0e9256984167b650ec6664754b81a837628d3ff63bcd0a6d06620
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/top40/results" "$root/top40/failures"
ont=ore_ont_${id}.owl
out=$root/top40/results/$ont.json
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm v110_candidate_v5_top40 \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-v110-v5-top40-${SLURM_JOB_ID}" \
  --failures-dir "$root/top40/failures" \
  --checkpoint "$root/top40/results/$ont.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print({k:r.get(k) for k in ("ont","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo TOP40_COMPLETE ontology="$id"
