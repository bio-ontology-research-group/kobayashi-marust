#!/bin/bash
#SBATCH --job-name=km-flat-leaf-9794
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:06:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-flat-leaf-20260825/functional/slurm-9794-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-flat-leaf-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
ont=ore_ont_9794.owl
sha=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$sha" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
out="$root/functional/results/9794.json"
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm flat_leaf_candidate \
  --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-flat-leaf-${SLURM_JOB_ID}-9794" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/9794.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$sha" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "flat_nf1", r
assert r["subsumptions"] == 0 and r["unsatisfiable"] == 0 and r["consistent"], r
PY
mv "$out.tmp" "$out"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print(json.dumps({k:r[k] for k in ["ont","wall_s","peak_mb","selected_route_trace","signature_sha256"]},sort_keys=True))
PY
echo FUNCTIONAL_COMPLETE ontology=9794
