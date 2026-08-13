#!/bin/bash
#SBATCH --job-name=km-78d5674-7914
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813/verify-%j.out
set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-78d5674-atomic-abox-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/results" "$root/failures"
for route in ht_bridge auto; do
  ont=ore_ont_7914.owl
  work=${SLURM_TMPDIR:-/tmp}/km-78d5674-$route-$SLURM_JOB_ID
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "atomic_$route" --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
    --checkpoint "$root/results/$ont.$route.checkpoint.json" --capture-km-route \
    --env "KM_ROUTE=$route" > "$root/results/$ont.$route.json.tmp"
  /usr/bin/python3 - "$root/results/$ont.$route.json.tmp" "$ont" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2] and r["binary_sha256"] == sys.argv[3]
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
PY
  mv "$root/results/$ont.$route.json.tmp" "$root/results/$ont.$route.json"
done
echo VERIFY_COMPLETE ontology=ore_ont_7914.owl
