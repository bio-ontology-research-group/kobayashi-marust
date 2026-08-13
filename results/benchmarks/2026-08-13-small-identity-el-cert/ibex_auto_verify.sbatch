#!/bin/bash
#SBATCH --job-name=km-fd30da7-auto
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-fd30da7-identity-elcert-20260813/auto-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-fd30da7-identity-elcert-20260813
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected=$(cut -d' ' -f1 "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
ont=ore_ont_15803.owl
mkdir -p "$root/auto-results" "$root/auto-failures"
work=${SLURM_TMPDIR:-/tmp}/km-fd30da7-auto-${SLURM_JOB_ID}
PYTHONPATH="$harness" /usr/bin/python3 -c 'import full_panel_run_one, ore_canon, tree_watchdog'
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm fd30da7_auto --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude --workdir "$work" --failures-dir "$root/auto-failures" \
  --checkpoint "$root/auto-results/$ont.checkpoint.json" --capture-km-route \
  --env KM_ROUTE=auto > "$root/auto-results/$ont.json.tmp"
/usr/bin/python3 - "$root/auto-results/$ont.json.tmp" "$ont" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2]
assert r["binary_sha256"] == sys.argv[3]
assert r["checkpointed"]
assert r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "certified_el_production", r
PY
mv "$root/auto-results/$ont.json.tmp" "$root/auto-results/$ont.json"
echo AUTO_COMPLETE ontology=$ont
