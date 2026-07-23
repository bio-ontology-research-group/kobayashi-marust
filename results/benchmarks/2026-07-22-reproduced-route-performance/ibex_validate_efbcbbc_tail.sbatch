#!/bin/bash
# Exact runtime gate for the merged 10621+9540 source revision.
# Tasks 0-3 require KM full-IRI identity through public and automatic routes,
# task 4 proves the 10621 bridge still defers on 4669, and tasks 5-6 rerun the
# matching Konclude references from source-bound binaries.
#SBATCH --job-name=km-efbcbbc-gate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-6%7
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/tail-final-efbcbbc/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "tail gate failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

sentinel=__km_efbcbbc_clean_v1__
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

root=/ibex/scratch/hohndor/km/tail-final-efbcbbc
binary=$root/bin/km-efbcbbc-ibex
receipt=$root/bin/km-efbcbbc-ibex.receipt.json
runner=$root/drivers/validate_tail_runner.py
fingerprinter=$root/drivers/full_panel_fingerprint.py
ontology_10621=/ibex/scratch/hohndor/km/corpus/ore_ont_10621.owl
ontology_9540=/ibex/scratch/hohndor/km/corpus/ore_ont_9540.owl
ontology_4669=/ibex/scratch/hohndor/km/corpus/ore_ont_4669.owl
konclude_root=/ibex/scratch/hohndor/km/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
konclude=$konclude_root/Konclude-build-a
konclude_lib=$konclude_root/runtime-lib
konclude_manifest=$konclude_root/runtime-files.sha256

sha_of() { /usr/bin/sha256sum "$1" | /usr/bin/cut -d ' ' -f1; }
[[ $(sha_of "$ontology_10621") == 5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167 ]]
[[ $(sha_of "$ontology_9540") == d6ce184d69fee10fc8c78753611fcb86b43123b58268c6d6ed3415e78fda4b04 ]]
[[ $(sha_of "$ontology_4669") == 2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb ]]
[[ $(sha_of "$runner") == 8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4 ]]
[[ $(sha_of "$fingerprinter") == ab1fe611ceeda8e4b2c58e8c9814a45148cc1186ec2821e2369d7446c076214b ]]
[[ $(sha_of "$konclude") == e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4 ]]
[[ -s $konclude_manifest && -d $konclude_lib ]]

binary_sha=$(/usr/bin/python3 - "$receipt" "$binary" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

receipt_path, binary_path = map(Path, sys.argv[1:])
record = json.loads(receipt_path.read_text())
assert record["source_revision"] == "efbcbbc57193bd5a50b0ee8f07c25114414fc01d"
assert record["source_archive_sha256"] == "bd341a082183cf33f483e9a567b9b54d052a333a5985d97581c143e57e6dbf4c"
assert Path(record["binary"]) == binary_path
digest = hashlib.sha256(binary_path.read_bytes()).hexdigest()
assert record["binary_sha256"] == digest
print(digest)
PY
)

out=$root/results/$SLURM_ARRAY_JOB_ID/task-$SLURM_ARRAY_TASK_ID
/usr/bin/mkdir -p "$out"

if (( SLURM_ARRAY_TASK_ID <= 3 )); then
    case $SLURM_ARRAY_TASK_ID in
        0)
            ontology=$ontology_10621
            route=certified_nominals
            expected_trace=certified_nominals
            expected_sha=066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e
            expected_sub=70827
            expected_unsat=33433
            ;;
        1)
            ontology=$ontology_10621
            route=auto
            expected_trace=certified_nominals
            expected_sha=066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e
            expected_sub=70827
            expected_unsat=33433
            ;;
        2)
            ontology=$ontology_9540
            route=certified_card_nominals
            expected_trace=certified_card_nominals
            expected_sha=7900df779b1752466c62035cc6ca5bfe275351085ebcc842cbd87c960a59137b
            expected_sub=66
            expected_unsat=0
            ;;
        3)
            ontology=$ontology_9540
            route=auto
            expected_trace=certified_card_nominals
            expected_sha=7900df779b1752466c62035cc6ca5bfe275351085ebcc842cbd87c960a59137b
            expected_sub=66
            expected_unsat=0
            ;;
    esac
    /usr/bin/python3 -I "$runner" \
        --kind km --label "$(basename "$ontology")-$route" \
        --ontology "$ontology" --binary "$binary" \
        --output-dir "$out/run" --timeout 240 --memcap-mb 20480 \
        --env "KM_ROUTE=$route" --env KM_TIMING=1 \
        --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18
    /usr/bin/python3 -I "$fingerprinter" \
        --input "$out/run/stdout.log" --format json \
        --source-ontology "$ontology" --output-prefix "$out/taxonomy"
    /usr/bin/python3 - "$out/run/run.json" "$out/taxonomy.json" \
        "$out/run/stderr.log" "$binary_sha" "$expected_trace" "$expected_sha" \
        "$expected_sub" "$expected_unsat" <<'PY'
import json
from pathlib import Path
import sys

run = json.loads(Path(sys.argv[1]).read_text())
taxonomy = json.loads(Path(sys.argv[2]).read_text())
stderr = Path(sys.argv[3]).read_text(errors="replace")
binary_sha, trace, expected_sha = sys.argv[4:7]
expected_sub, expected_unsat = map(int, sys.argv[7:9])
assert run["status"] == "ok", run
assert run["binary_sha256"] == binary_sha, run
assert taxonomy["taxonomy_sha256"] == expected_sha, taxonomy
assert taxonomy["subsumptions"] == expected_sub, taxonomy
assert taxonomy["unsatisfiable"] == expected_unsat, taxonomy
assert f"route={trace}" in stderr, stderr[-6000:]
if trace == "certified_nominals":
    assert "synchronous bridge classes=41647 typed_nominal=true cb_threads=1" in stderr, stderr[-6000:]
print(json.dumps({"accepted": True, "run": run, "taxonomy": taxonomy}, sort_keys=True))
PY
elif (( SLURM_ARRAY_TASK_ID == 4 )); then
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
    /usr/bin/python3 - "$out/run/run.json" "$out/run/stderr.log" "$binary_sha" <<'PY'
import json
from pathlib import Path
import sys

run = json.loads(Path(sys.argv[1]).read_text())
stderr = Path(sys.argv[2]).read_text(errors="replace")
assert run["status"] == "unsupported", run
assert run["binary_sha256"] == sys.argv[3], run
assert run["primary_output_bytes"] == 0, run
assert "route=ht_bridge" in stderr, stderr[-4000:]
assert "defer" in stderr.lower(), stderr[-4000:]
print(json.dumps({"accepted": True, "run": run}, sort_keys=True))
PY
else
    if (( SLURM_ARRAY_TASK_ID == 5 )); then
        ontology=$ontology_10621
        expected_sha=066b41b5f3e845110eceb3607b050627da744968ccef1ceafed50e3c3ea4468e
        expected_sub=70827
        expected_unsat=33433
    else
        ontology=$ontology_9540
        expected_sha=7900df779b1752466c62035cc6ca5bfe275351085ebcc842cbd87c960a59137b
        expected_sub=66
        expected_unsat=0
    fi
    /usr/bin/python3 -I "$runner" \
        --kind konclude --label "$(basename "$ontology")-fresh-konclude" \
        --ontology "$ontology" --binary "$konclude" \
        --output-dir "$out/run" --workers 16 --timeout 240 --memcap-mb 20480 \
        --env "LD_LIBRARY_PATH=$konclude_lib"
    /usr/bin/python3 -I "$fingerprinter" \
        --input "$out/run/taxonomy.owl" --format owlxml \
        --source-ontology "$ontology" --output-prefix "$out/taxonomy"
    /usr/bin/python3 - "$out/run/run.json" "$out/taxonomy.json" \
        "$expected_sha" "$expected_sub" "$expected_unsat" <<'PY'
import json
from pathlib import Path
import sys

run = json.loads(Path(sys.argv[1]).read_text())
taxonomy = json.loads(Path(sys.argv[2]).read_text())
assert run["status"] == "ok", run
assert taxonomy["taxonomy_sha256"] == sys.argv[3], taxonomy
assert taxonomy["subsumptions"] == int(sys.argv[4]), taxonomy
assert taxonomy["unsatisfiable"] == int(sys.argv[5]), taxonomy
print(json.dumps({"accepted": True, "run": run, "taxonomy": taxonomy}, sort_keys=True))
PY
fi

/usr/bin/sha256sum "$binary" "$receipt" "$runner" "$fingerprinter" \
    "$ontology_10621" "$ontology_9540" "$ontology_4669" "$konclude" \
    "$konclude_manifest" > "$out/inputs.sha256"
/usr/bin/printf 'TAIL_GATE_ACCEPTED task=%s binary_sha=%s\n' \
    "$SLURM_ARRAY_TASK_ID" "$binary_sha"
