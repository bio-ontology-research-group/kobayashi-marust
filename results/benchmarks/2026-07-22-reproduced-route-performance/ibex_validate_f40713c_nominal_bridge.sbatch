#!/bin/bash
# Targeted runtime gate for amended candidate 9047217 before integration.
# Tasks 0-2 require exact full-IRI equality for ORE 10621 through the forced,
# public certified, and automatic routes. Task 3 requires the repaired bridge
# to defer on ORE 4669. Task 4 independently reruns Konclude for 10621.
#SBATCH --job-name=km-f40713c-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-4%5
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/target-f40713c/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "target gate failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

sentinel=__km_f40713c_clean_v1__
if [[ $# -eq 0 ]]; then
    script=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?}" \
        SLURM_ARRAY_JOB_ID="${SLURM_ARRAY_JOB_ID:?}" \
        SLURM_ARRAY_TASK_ID="${SLURM_ARRAY_TASK_ID:?}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?}" \
        /bin/bash "$script" "$sentinel"
fi
[[ $# -eq 1 && $1 == "$sentinel" ]]
[[ $SLURM_CPUS_PER_TASK == 16 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

root=/ibex/scratch/hohndor/km/target-f40713c
binary=$root/bin/km-9047217-ibex
runner=$root/drivers/validate_tail_runner.py
fingerprinter=$root/drivers/full_panel_fingerprint.py
ontology_10621=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
ontology_4669=/ibex/scratch/hohndor/km/corpus/ore_ont_4669.owl
konclude=/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03/Konclude-build-a
konclude_lib=/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03/runtime-lib

sha_of() { /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'; }
[[ $(sha_of "$binary") == 92b75c0972fff9babd5c02556f254ac6c3f2eda0a6b2d08ce011b1e634490e39 ]]
[[ $(sha_of "$ontology_10621") == 5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167 ]]
[[ $(sha_of "$ontology_4669") == 2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb ]]
[[ $(sha_of "$konclude") == e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4 ]]
for path in "$runner" "$fingerprinter"; do [[ -s $path ]]; done

out=$root/results/$SLURM_ARRAY_JOB_ID/task-$SLURM_ARRAY_TASK_ID
/usr/bin/mkdir -p "$out"

if (( SLURM_ARRAY_TASK_ID <= 2 )); then
    case $SLURM_ARRAY_TASK_ID in
        0) route=ht_bridge; expected_trace=ht_bridge ;;
        1) route=certified_nominals; expected_trace=certified_nominals ;;
        2) route=auto; expected_trace=certified_nominals ;;
    esac
    /usr/bin/python3 -I "$runner" \
        --kind km --label "10621-$route" \
        --ontology "$ontology_10621" --binary "$binary" \
        --output-dir "$out/run" --timeout 240 --memcap-mb 20480 \
        --env "KM_ROUTE=$route" --env KM_TIMING=1 \
        --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18
    /usr/bin/python3 -I "$fingerprinter" \
        --input "$out/run/stdout.log" --format json \
        --source-ontology "$ontology_10621" --output-prefix "$out/taxonomy"
    /usr/bin/python3 - "$out/run/run.json" "$out/taxonomy.json" \
        "$out/run/stderr.log" "$expected_trace" <<'PY'
import json
from pathlib import Path
import sys
run = json.loads(Path(sys.argv[1]).read_text())
tax = json.loads(Path(sys.argv[2]).read_text())
stderr = Path(sys.argv[3]).read_text(errors="replace")
trace = sys.argv[4]
assert run["status"] == "ok", run
assert run["binary_sha256"] == "92b75c0972fff9babd5c02556f254ac6c3f2eda0a6b2d08ce011b1e634490e39"
assert tax["taxonomy_sha256"] == "066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e", tax
assert tax["subsumptions"] == 70827, tax
assert tax["unsatisfiable"] == 33433, tax
assert f"route={trace}" in stderr, stderr[-4000:]
if trace == "certified_nominals":
    assert "synchronous bridge classes=41647 typed_nominal=true cb_threads=1" in stderr, stderr[-4000:]
print(json.dumps({"accepted": True, "run": run, "taxonomy": tax}, sort_keys=True))
PY
elif (( SLURM_ARRAY_TASK_ID == 3 )); then
    set +e
    /usr/bin/python3 -I "$runner" \
        --kind km --label 4669-bridge-defer \
        --ontology "$ontology_4669" --binary "$binary" \
        --output-dir "$out/run" --timeout 240 --memcap-mb 20480 \
        --env KM_ROUTE=ht_bridge --env KM_TIMING=1 \
        --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18
    runner_rc=$?
    set -e
    [[ $runner_rc -ne 0 ]]
    /usr/bin/python3 - "$out/run/run.json" "$out/run/stderr.log" <<'PY'
import json
from pathlib import Path
import sys
run = json.loads(Path(sys.argv[1]).read_text())
stderr = Path(sys.argv[2]).read_text(errors="replace")
assert run["status"] == "unsupported", run
assert run["binary_sha256"] == "92b75c0972fff9babd5c02556f254ac6c3f2eda0a6b2d08ce011b1e634490e39"
assert run["primary_output_bytes"] == 0, run
assert "route=ht_bridge" in stderr, stderr[-4000:]
assert "defer" in stderr.lower(), stderr[-4000:]
print(json.dumps({"accepted": True, "run": run}, sort_keys=True))
PY
else
    /usr/bin/python3 -I "$runner" \
        --kind konclude --label 10621-fresh-konclude \
        --ontology "$ontology_10621" --binary "$konclude" \
        --output-dir "$out/run" --workers 16 --timeout 240 --memcap-mb 20480 \
        --env "LD_LIBRARY_PATH=$konclude_lib"
    /usr/bin/python3 -I "$fingerprinter" \
        --input "$out/run/taxonomy.owl" --format owlxml \
        --source-ontology "$ontology_10621" --output-prefix "$out/taxonomy"
    /usr/bin/python3 - "$out/run/run.json" "$out/taxonomy.json" <<'PY'
import json
from pathlib import Path
import sys
run = json.loads(Path(sys.argv[1]).read_text())
tax = json.loads(Path(sys.argv[2]).read_text())
assert run["status"] == "ok", run
assert tax["taxonomy_sha256"] == "066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e", tax
assert tax["subsumptions"] == 70827, tax
assert tax["unsatisfiable"] == 33433, tax
print(json.dumps({"accepted": True, "run": run, "taxonomy": tax}, sort_keys=True))
PY
fi

/usr/bin/sha256sum "$binary" "$runner" "$fingerprinter" \
    "$ontology_10621" "$ontology_4669" > "$out/inputs.sha256"
/usr/bin/printf 'TARGET_GATE_ACCEPTED task=%s\n' "$SLURM_ARRAY_TASK_ID"
