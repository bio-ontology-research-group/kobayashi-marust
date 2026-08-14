#!/bin/bash
#SBATCH --job-name=km-6934-auto-candidate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/6934-general-isolation-20260814/auto-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/6934-general-isolation-20260814
binary=$root/km
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz
(cd "$root" && sha256sum -c km.sha256)
out=$root/auto-results
mkdir -p "$out" "$root/auto-failures"
work=${SLURM_TMPDIR:-/tmp}/km-6934-auto-$SLURM_JOB_ID
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm auto_general_ground --ontology "$ontology" --binary "$binary" \
  --workers 16 --timeout 60 --memcap-mb 20480 --gold "$gold" \
  --gold-kind konclude --workdir "$work" --failures-dir "$root/auto-failures" \
  --checkpoint "$out/result.checkpoint.json" --capture-km-route \
  --env KM_ROUTE=auto --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
  --env KM_HT_MEM_GB=18 > "$out/result.json.tmp"
mv "$out/result.json.tmp" "$out/result.json"
/usr/bin/python3 - "$out/result.json" <<'PY'
import json, sys

r = json.load(open(sys.argv[1]))
assert r["status"] == "ok", r
assert r["verdict"] == "match", r
assert r["signature_sha256"] == "5e60a794400802833a9d5785abb6320b7b13d702e48a4c810462bad6c1fc931e", r
assert r["selected_route_trace"] == "ht_general", r
PY
jq -c '{status,verdict,wall_s,peak_mb,signature_sha256,selected_route_trace,binary_sha256}' \
  "$out/result.json"
