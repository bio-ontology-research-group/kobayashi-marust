#!/bin/bash
# Complete source-bound acceptance sweep with one exclusive allocation per
# ontology. The Slurm allocation exceeds the reasoner cap so the Python
# supervisor survives a watchdog race and can publish a terminal memout row.
#SBATCH --job-name=km-main592x
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --exclusive
#SBATCH --array=0-591%10
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/integrated-main-full-20260730/slurm-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/integrated-main-full-20260730
km_root=/ibex/scratch/hohndor/km
ontology_list=$km_root/routing_20260715/onts.txt
index=${SLURM_ARRAY_TASK_ID:?}
[[ $index =~ ^([0-9]|[1-9][0-9]|[1-5][0-9][0-9])$ ]]
(( index < 592 ))
[[ $(/usr/bin/wc -l < "$ontology_list") -eq 592 ]]
ontology=$(/usr/bin/sed -n "$((index + 1))p" "$ontology_list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
[[ ! -e "$root/results/$ontology.json" ]]

work=${SLURM_TMPDIR:-/tmp}/km-main592x-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/results" "$root/profiles" "$root/failures"
/usr/bin/cp "$km_root/corpus/$ontology" "$work/$ontology"

/usr/bin/python3 "$root/full_panel_run_one.py" \
  --kind km \
  --arm km_route_auto_integrated_main_exclusive \
  --ontology "$work/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" \
  --env KM_ROUTE=auto \
  > "$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$ontology" "$index" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2]:
    raise SystemExit(f"ontology mismatch: {row.get('ont')} != {sys.argv[2]}")
if row.get("slurm_array_task_id") != str(sys.argv[3]):
    raise SystemExit(
        f"task mismatch: {row.get('slurm_array_task_id')} != {sys.argv[3]}"
    )
if not row.get("checkpointed"):
    raise SystemExit(f"runner did not checkpoint terminal state: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
PY
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"

# Profiling parses the ontology independently from `classify`.  It is useful
# routing evidence, but it must never be able to erase the authoritative
# terminal result above.  In particular, run it only after publishing that
# result and constrain its address space separately from the Slurm allocation.
profile_tmp="$root/profiles/$ontology.json.tmp"
profile_err="$root/profiles/$ontology.err.tmp"
if timeout 240 /usr/bin/prlimit --as=25769803776 -- \
    "$root/km" profile "$work/$ontology" > "$profile_tmp" 2> "$profile_err" \
  && /usr/bin/python3 - "$profile_tmp" "$ontology" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[2] or row.get("status") != "ok":
    raise SystemExit(f"invalid profile row: {row}")
if not row.get("selected_route"):
    raise SystemExit(f"missing selected route: {row}")
PY
then
  /usr/bin/mv "$profile_tmp" "$root/profiles/$ontology.json"
  /usr/bin/rm -f "$profile_err"
else
  profile_rc=$?
  /usr/bin/python3 - "$ontology" "$profile_rc" "$profile_err" > "$profile_tmp" <<'PY'
import json
import pathlib
import sys

err = pathlib.Path(sys.argv[3])
print(json.dumps({
    "ont": sys.argv[1],
    "status": "error",
    "selected_route": None,
    "returncode": int(sys.argv[2]),
    "error": err.read_text(errors="replace")[-4000:] if err.exists() else "",
}))
PY
  /usr/bin/mv "$profile_tmp" "$root/profiles/$ontology.json"
  /usr/bin/mv "$profile_err" "$root/profiles/$ontology.err"
fi
echo "TASK_COMPLETE index=$index ontology=$ontology"
