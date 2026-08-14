#!/bin/bash
#SBATCH --job-name=km-6934-retained-route
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/route-6934-v020-20260814/retained-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/route-6934-v020-20260814
binary=/ibex/scratch/hohndor/km/routing_20260715/retained-route-rerun-20260718/target/release/km
expected=dce27171c9d9d2753c55672266289ccec3e8ab74f7f47d75b20f8375e0c84aee
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/retained-results" "$root/retained-failures"
work=${SLURM_TMPDIR:-/tmp}/km-6934-retained-$SLURM_JOB_ID
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm retained_htforce_race \
  --ontology "$ontology" --binary "$binary" --workers 16 \
  --timeout 60 --memcap-mb 20480 --gold "$gold" --gold-kind konclude \
  --workdir "$work" --failures-dir "$root/retained-failures" \
  --checkpoint "$root/retained-results/retained.checkpoint.json" \
  --capture-km-route \
  --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18 \
  --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_ABSORB=1 \
  --env KM_ABSORB_PORTFOLIO=1 --env KM_HT_FORCE=1 --env KM_HT_MODE=race \
  > "$root/retained-results/retained.json.tmp"
mv "$root/retained-results/retained.json.tmp" \
  "$root/retained-results/retained.json"
/usr/bin/python3 - "$root/retained-results/retained.json" <<'PY'
import json, sys

r = json.load(open(sys.argv[1]))
assert r["binary_sha256"] == "dce27171c9d9d2753c55672266289ccec3e8ab74f7f47d75b20f8375e0c84aee"
assert r["checkpointed"]
print(json.dumps({key: r.get(key) for key in (
    "status", "verdict", "wall_s", "peak_mb", "signature_sha256",
    "selected_route_trace", "binary_sha256")}, sort_keys=True))
PY
