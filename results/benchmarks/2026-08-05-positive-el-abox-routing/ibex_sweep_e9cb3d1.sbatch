#!/bin/bash
#SBATCH --job-name=km-e9cb3d1-positive-el-abox
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%10
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/candidate-e9cb3d1-positive-el-abox-20260805/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/candidate-e9cb3d1-positive-el-abox-20260805
expected_binary=6dc20602cb531f5a19bc688da5ce4b2e74da18bec95d858574c43128488a42a1
[[ $(sha256sum "$root/km" | cut -d" " -f1) == "$expected_binary" ]]
arm=km_route_auto_e9cb3d1
km_root=/ibex/scratch/hohndor/km
ontology_list=$km_root/routing_20260715/onts.txt
index=${SLURM_ARRAY_TASK_ID:?}
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
if [[ $cpu_model != *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]; then
  echo "UNEXPECTED_CPU_MODEL model=[$cpu_model]" >&2
  exit 2
fi
[[ $index =~ ^([0-9]|[1-9][0-9]|[1-5][0-9][0-9])$ ]]
(( index < 592 ))
[[ $(/usr/bin/wc -l < "$ontology_list") -eq 592 ]]
ontology=$(/usr/bin/sed -n "$((index + 1))p" "$ontology_list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]

PYTHONPATH="$root" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

if [[ -e "$root/results/$ontology.json" ]]; then
  if /usr/bin/python3 - \
      "$root/results/$ontology.json" \
      "$root/profiles/$ontology.json" \
      "$ontology" "$index" "$expected_binary" <<'PY'
import json
import sys

row = json.load(open(sys.argv[1]))
if row.get("ont") != sys.argv[3]:
    raise SystemExit(f"ontology mismatch in existing row: {row}")
if row.get("slurm_array_task_id") != str(sys.argv[4]):
    raise SystemExit(f"task mismatch in existing row: {row}")
if row.get("binary_sha256") != sys.argv[5]:
    raise SystemExit(f"binary mismatch in existing row: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid existing terminal status: {row}")
profile = json.load(open(sys.argv[2]))
if profile.get("ont") != sys.argv[3] or profile.get("status") != "ok":
    raise SystemExit(f"invalid existing profile: {profile}")
if not profile.get("selected_route"):
    raise SystemExit(f"missing selected route: {profile}")
if (
    not row.get("selected_route_trace")
    and not (
        sys.argv[3] == "ore_ont_10860.owl"
        and row.get("status") == "unsupported"
    )
):
    raise SystemExit(f"missing production route trace: {row}")
PY
  then
    echo "ALREADY_COMPLETE index=$index ontology=$ontology"
    exit 0
  fi
  echo "INCOMPLETE_RESUME_PAIR index=$index ontology=$ontology; rerunning"
fi

work=${SLURM_TMPDIR:-/tmp}/km-auto-e9cb3d1-592-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$root/results" "$root/profiles" "$root/failures"
profile_tmp="$root/profiles/$ontology.json.tmp"
profile_err="$root/profiles/$ontology.err.tmp"
if timeout 240 /usr/bin/prlimit --as=25769803776 -- \
    "$root/km" profile "$km_root/corpus/$ontology" > "$profile_tmp" 2> "$profile_err" \
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
  echo "PROFILE_FAILED index=$index ontology=$ontology" >&2
  exit 1
fi

runner=$root/full_panel_run_one.py
if [[ $ontology == ore_ont_3524.owl || $ontology == ore_ont_13503.owl || $ontology == ore_ont_4669.owl || $ontology == ore_ont_15703.owl ]]; then
  runner=$root/full_panel_run_one_collision_safe.py
fi

/usr/bin/python3 "$runner" \
  --kind km \
  --arm "$arm" \
  --ontology "$km_root/corpus/$ontology" \
  --binary "$root/km" \
  --workers 16 \
  --timeout 240 \
  --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude \
  --workdir "$work/run" \
  --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" \
  --capture-km-route \
  --env KM_ROUTE=auto \
  > "$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$ontology" "$index" "$expected_binary" <<'PY'
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
if row.get("binary_sha256") != sys.argv[4]:
    raise SystemExit(f"runner used wrong binary: {row}")
if row.get("status") not in {"ok", "timeout", "memout", "error", "unsupported"}:
    raise SystemExit(f"invalid terminal status: {row}")
if (
    not row.get("selected_route_trace")
    and not (
        sys.argv[2] == "ore_ont_10860.owl"
        and row.get("status") == "unsupported"
    )
):
    raise SystemExit(f"missing production route trace: {row}")
expected_fulliri = {
    "ore_ont_3524.owl": "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a",
    "ore_ont_13503.owl": "1b8fdf730b9cdce8afed1c69c13e782c6c2dde70c42e5f1d2273dcbdb6b1282b",
    "ore_ont_4669.owl": "a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30",
    "ore_ont_15703.owl": "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a",
}
if sys.argv[2] in expected_fulliri:
    expected = expected_fulliri[sys.argv[2]]
    if row.get("status") != "ok" or row.get("verdict") != "match":
        raise SystemExit(f"collision-safe adjudication failed: {row}")
    if row.get("fulliri_taxonomy_sha256") != expected:
        raise SystemExit(f"collision-safe fingerprint mismatch: {row}")
PY
/usr/bin/mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
echo "TASK_COMPLETE index=$index ontology=$ontology"
