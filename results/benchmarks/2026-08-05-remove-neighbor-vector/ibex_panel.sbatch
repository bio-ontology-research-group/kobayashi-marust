#!/bin/bash
#SBATCH --job-name=km-no-neighbor-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=33,109,157,258,289,362,415,435,518,558
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/remove-neighbor-vector-20260805/slurm-%A_%a.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/remove-neighbor-vector-20260805
km_root=/ibex/scratch/hohndor/km
ontology_list=$km_root/routing_20260715/onts.txt
index=${SLURM_ARRAY_TASK_ID:?}

[[ -x $root/km && -s $root/km.sha256 ]]
expected_binary=$(cut -d' ' -f1 < "$root/km.sha256")
[[ $expected_binary =~ ^[0-9a-f]{64}$ ]]
[[ $(sha256sum "$root/km" | cut -d' ' -f1) == "$expected_binary" ]]
[[ $(wc -l < "$ontology_list") -eq 592 ]]
ontology=$(sed -n "$((index + 1))p" "$ontology_list")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]

PYTHONPATH="$root" /usr/bin/python3 -c \
  'import full_panel_fingerprint, full_panel_run_one, full_panel_run_one_collision_safe, full_panel_run_one_fulliri_only, ore_canon, tree_watchdog'

mkdir -p "$root/results" "$root/profiles" "$root/failures"
if [[ -e $root/results/$ontology.json ]]; then
  /usr/bin/python3 - "$root/results/$ontology.json" "$root/profiles/$ontology.json" \
      "$ontology" "$index" "$expected_binary" <<'PY'
import json, sys
row = json.load(open(sys.argv[1]))
profile = json.load(open(sys.argv[2]))
assert row["ont"] == sys.argv[3]
assert row["slurm_array_task_id"] == sys.argv[4]
assert row["binary_sha256"] == sys.argv[5]
assert row["status"] in {"ok", "timeout", "memout", "error", "unsupported"}
assert row.get("checkpointed")
assert profile["ont"] == sys.argv[3] and profile["status"] == "ok"
assert profile.get("selected_route")
PY
  echo "ALREADY_COMPLETE index=$index ontology=$ontology"
  exit 0
fi

profile_tmp=$root/profiles/$ontology.json.tmp
timeout 240 /usr/bin/prlimit --as=25769803776 -- \
  "$root/km" profile "$km_root/corpus/$ontology" > "$profile_tmp"
/usr/bin/python3 - "$profile_tmp" "$ontology" <<'PY'
import json, sys
row = json.load(open(sys.argv[1]))
assert row["ont"] == sys.argv[2] and row["status"] == "ok"
assert row.get("selected_route")
PY
mv "$profile_tmp" "$root/profiles/$ontology.json"

runner=$root/full_panel_run_one.py
if [[ $ontology == ore_ont_4669.owl ]]; then
  runner=$root/full_panel_run_one_collision_safe.py
fi
work=${SLURM_TMPDIR:-/tmp}/km-no-neighbor-panel-$SLURM_JOB_ID
/usr/bin/python3 "$runner" \
  --kind km --arm km_no_neighbor_4275690 \
  --ontology "$km_root/corpus/$ontology" --binary "$root/km" \
  --workers 16 --timeout 240 --memcap-mb 20480 \
  --gold "$km_root/cmp2/out/konclude/konclude__$ontology.sig.gz" \
  --gold-kind konclude --workdir "$work/run" --failures-dir "$root/failures" \
  --checkpoint "$root/results/$ontology.checkpoint.json" --capture-km-route \
  --env KM_ROUTE=auto > "$root/results/$ontology.json.tmp"

/usr/bin/python3 - "$root/results/$ontology.json.tmp" "$ontology" "$index" "$expected_binary" <<'PY'
import json, sys
row = json.load(open(sys.argv[1]))
assert row["ont"] == sys.argv[2]
assert row["slurm_array_task_id"] == sys.argv[3]
assert row["binary_sha256"] == sys.argv[4]
assert row.get("checkpointed")
assert row["status"] in {"ok", "timeout", "memout", "error", "unsupported"}
if sys.argv[2] == "ore_ont_4669.owl":
    assert row["status"] == "ok" and row["verdict"] == "match"
    assert row["fulliri_taxonomy_sha256"] == "a482e066a22110df593bf3a4c1fdd0ef4404f7141903b2101b85aae49811cb30"
PY
mv "$root/results/$ontology.json.tmp" "$root/results/$ontology.json"
echo "TASK_COMPLETE index=$index ontology=$ontology binary_sha256=$expected_binary"
