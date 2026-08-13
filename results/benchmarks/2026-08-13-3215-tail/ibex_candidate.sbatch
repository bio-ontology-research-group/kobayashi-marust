#!/bin/bash
# Exact-gold targeted acceptance test for the pre-certificate disjunction hoist.
#SBATCH --job-name=km-3215-hoist
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-3215-precert-hoist-20260813/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-3215-precert-hoist-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/results" "$root/failures"
"$root/km" profile /ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl \
  > "$root/results/profile.json.tmp"
mv "$root/results/profile.json.tmp" "$root/results/profile.json"
work=${SLURM_TMPDIR:-/tmp}/km-3215-hoist-$SLURM_JOB_ID
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm 3215_precert_hoist \
  --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_3215.owl \
  --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_3215.owl.sig.gz \
  --gold-kind konclude --workdir "$work" --failures-dir "$root/failures" \
  --checkpoint "$root/results/elc_cert.checkpoint.json" --capture-km-route \
  --env KM_ROUTE=elc_cert > "$root/results/elc_cert.json.tmp"
python3 - "$root/results/elc_cert.json.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2] and r["checkpointed"], r
assert r["status"] in {"ok","timeout","memout","error","unsupported"}, r
PY
mv "$root/results/elc_cert.json.tmp" "$root/results/elc_cert.json"
echo CANDIDATE_COMPLETE
