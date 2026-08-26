#!/bin/bash
#SBATCH --job-name=km-builtin-flat-functional
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --nodes=1
#SBATCH --oversubscribe
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=20G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825/functional/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v110-builtin-flat-20260825
harness=/ibex/scratch/hohndor/km/v110-baseline-20260825/full-sweep
expected=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/functional/results" "$root/functional/failures"
out="$root/functional/results/ore_ont_3524.owl.json"
/usr/bin/python3 "$harness/full_panel_run_one_collision_safe.py" \
  --kind km --arm builtin_flat_functional \
  --ontology /ibex/scratch/hohndor/km/corpus/ore_ont_3524.owl \
  --binary "$root/km" --workers 4 --timeout 240 --memcap-mb 20480 \
  --gold /ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_3524.owl.sig.gz \
  --gold-kind konclude \
  --workdir "${SLURM_TMPDIR:-/tmp}/km-builtin-flat-functional-${SLURM_JOB_ID}" \
  --failures-dir "$root/functional/failures" \
  --checkpoint "$root/functional/results/ore_ont_3524.owl.checkpoint.json" \
  --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
/usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2], r
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "flat_nf1", r
assert r["fulliri_taxonomy_sha256"] == "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a", r
assert r["fulliri_subsumptions"] == 1604386 and r["fulliri_unsatisfiable"] == 0, r
PY
mv "$out.tmp" "$out"
cmp "$out" "$root/functional/results/ore_ont_3524.owl.checkpoint.json"
/usr/bin/python3 - "$out" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
print({key:r[key] for key in ("ont","wall_s","peak_mb","selected_route_trace","signature_sha256")})
PY
echo BUILTIN_FLAT_FUNCTIONAL_COMPLETE
