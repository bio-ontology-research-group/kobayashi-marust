#!/bin/bash
#SBATCH --job-name=km-large-elcert-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/large-elcert-panel-20260813/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/large-elcert-panel-20260813
source_root=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
expected_binary=1abb488945d16df5ba16ee6aa261b1a2aac356b2bfe183b256856c7e28fe9734
[[ $(sha256sum "$source_root/km" | cut -d" " -f1) == "$expected_binary" ]]
onts=(ore_ont_8737.owl ore_ont_16744.owl ore_ont_7246.owl)
ont=${onts[${SLURM_ARRAY_TASK_ID:?}]}
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

PYTHONPATH="$source_root" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

mkdir -p "$root/results" "$root/failures"
work=${SLURM_TMPDIR:-/tmp}/km-large-elcert-${SLURM_JOB_ID}-${SLURM_ARRAY_TASK_ID}
for route in production_all elc elc_cert; do
  out="$root/results/${ont}__${route}.json"
  if [[ -s "$out" ]] && python3 - "$out" "$ont" "$route" "$expected_binary" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2]
assert r["binary_sha256"] == sys.argv[4]
assert r["checkpointed"]
assert r["selected_route_trace"] == sys.argv[3]
PY
  then
    continue
  fi
  /usr/bin/python3 "$source_root/full_panel_run_one.py" \
    --kind km --arm "large_elcert_${route}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$source_root/km" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$route" --failures-dir "$root/failures" \
    --checkpoint "$root/results/${ont}__${route}.checkpoint.json" \
    --capture-km-route --env "KM_ROUTE=$route" > "$out.tmp"
  python3 - "$out.tmp" "$ont" "$route" "$expected_binary" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["ont"] == sys.argv[2]
assert r["binary_sha256"] == sys.argv[4]
assert r["checkpointed"]
assert r["selected_route_trace"] == sys.argv[3]
assert r["status"] in {"ok","timeout","memout","error","unsupported"}
PY
  mv "$out.tmp" "$out"
done

python3 - "$root/results" "$ont" <<'PY'
import json,pathlib,sys
root=pathlib.Path(sys.argv[1]); ont=sys.argv[2]
rows=[json.load(open(root/f"{ont}__{route}.json")) for route in ("production_all","elc","elc_cert")]
ok=[r for r in rows if r["status"] == "ok"]
if len({r.get("signature_sha256") for r in ok}) != 1:
    raise SystemExit(f"successful signatures differ: {rows}")
print(json.dumps({"ont":ont,"rows":rows},sort_keys=True))
PY
echo PANEL_COMPLETE ontology=$ont
