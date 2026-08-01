#!/bin/bash
# Complete collision-safe 55-arm rerun for the two non-injective ORE cases.
# Each successful answer is full-IRI fingerprinted and deleted before the next
# arm, avoiding the legacy local-name canonicalizer and supervisor OOM.
#SBATCH --job-name=km-v020-collision-panel
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=12:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --array=121,552
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/release-v020-uniform-20260801/collision-rerun/slurm-%A_%a.out

set -euo pipefail
trap 'rc=$?; printf "COLLISION_PANEL_FAILED line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

root=/ibex/scratch/hohndor/km/release-v020-uniform-20260801
drivers=$root/drivers
build=$root/build
km_root=/ibex/scratch/hohndor/km
jdk=$km_root/bench/jdk8u492-b09
konclude=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
result_root=$root/collision-rerun/runs/$SLURM_ARRAY_JOB_ID
work_root=$root/collision-rerun/work/$SLURM_ARRAY_JOB_ID
task_tmp=${SLURM_TMPDIR:-$root/collision-rerun/tmp-$SLURM_JOB_ID}/km-panel-$SLURM_ARRAY_TASK_ID

export JAVA_HOME=$jdk
export PATH=$JAVA_HOME/bin:/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0
export RAYON_NUM_THREADS=16
export TMPDIR=$task_tmp
umask 0027
/usr/bin/mkdir -p "$result_root" "$work_root" "$task_tmp"

for required in \
    "$drivers/full_panel_contract.py" \
    "$drivers/full_panel_run_one.py" \
    "$drivers/full_panel_run_one_collision_safe.py" \
    "$drivers/full_panel_run_one_fulliri_only.py" \
    "$drivers/full_panel_fingerprint.py" \
    "$drivers/run_full_panel_ontology.py" \
    "$build/build-receipt.json" \
    "$build/bin/km-main"
do
    [[ -e $required ]] || { echo "missing benchmark input: $required" >&2; exit 2; }
done

/usr/bin/python3 "$drivers/run_full_panel_ontology.py" \
    --task-index "$SLURM_ARRAY_TASK_ID" \
    --ontology-list "$km_root/routing_20260715/onts.txt" \
    --corpus "$km_root/corpus" \
    --gold "$km_root/gold" \
    --build-root "$build" \
    --benchmark-root "$km_root/bench" \
    --result-root "$result_root" \
    --work-root "$work_root" \
    --runner "$drivers/full_panel_run_one_collision_safe.py" \
    --fingerprint "$drivers/full_panel_fingerprint.py" \
    --rustdl-adapter "$drivers/rustdl_json_adapter.py" \
    --sequoia-adapter "$drivers/sequoia_json_adapter.py" \
    --konclude "$konclude/Konclude-build-a" \
    --konclude-library "$konclude/runtime-lib" \
    --konclude-runtime-manifest "$konclude/runtime-files.sha256" \
    --elk "$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar" \
    --hermit-oracle "$build/bin/FullIriHermitOracle.class" \
    --hermit-classpath "$build/bin:$km_root/bench/hermit_cp/*" \
    --java "$jdk/bin/java" \
    --timeout 240 \
    --memcap-mb 20480

/usr/bin/python3 - "$result_root/results" "$SLURM_ARRAY_TASK_ID" <<'PY'
import json
import pathlib
import sys

expected_file = {
    "121": "ore_ont_3524.owl.jsonl",
    "552": "ore_ont_15703.owl.jsonl",
}.get(sys.argv[2])
if expected_file is None:
    raise SystemExit(f"unexpected collision-panel task {sys.argv[2]}")
result_file = pathlib.Path(sys.argv[1]) / expected_file
if not result_file.is_file():
    raise SystemExit(f"missing task result file {result_file}")
rows = [json.loads(line) for line in result_file.read_text().splitlines() if line]
if len(rows) != 55:
    raise SystemExit(f"expected 55 rows, found {len(rows)}")
arms = [row.get("arm") for row in rows]
if len(set(arms)) != 55:
    raise SystemExit(f"expected 55 unique arms, found {len(set(arms))}")
if any(row.get("status") == "harness_error" for row in rows):
    raise SystemExit("collision-safe rerun still contains harness_error")
expected_digest = "090129a7fbaa14652ada3408dd1f160e7dd4a09a3502cc3323d8dad734e8893a"
bad_ok = [
    row.get("arm")
    for row in rows
    if row.get("status") == "ok"
    and row.get("fulliri_taxonomy_sha256") != expected_digest
]
if bad_ok:
    raise SystemExit(f"successful rows with wrong full-IRI digest: {bad_ok}")
print(f"COLLISION_PANEL_VALID ontology={result_file.stem} rows=55 task={sys.argv[2]}")
PY
