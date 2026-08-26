#!/bin/bash
#SBATCH --job-name=km-stream-flat-more
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --array=0-1%1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-stream-flat-20260825/functional-more/slurm-%A_%a.out

set -euo pipefail
ids=(11395 3836)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/v110-stream-flat-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_${id}.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional-more/results" "$root/functional-more/failures"
out="$root/functional-more/results/${id}.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm stream_flat_more \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-stream-flat-more-${SLURM_JOB_ID}-${id}" \
  --failures-dir "$root/functional-more/failures" \
  --checkpoint "$root/functional-more/results/${id}.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "flat_nf1", r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print({k:r.get(k) for k in ("ont","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo STREAM_FLAT_MORE_COMPLETE ontology="$id"
