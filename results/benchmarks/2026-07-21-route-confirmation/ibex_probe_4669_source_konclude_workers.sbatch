#!/bin/bash
# Probe reproducible source-built Konclude routes for ORE 4669 with 1, 2, 4,
# and 8 workers. A completed full-IRI taxonomy is usable as an independent oracle;
# a timeout or memory failure remains a negative route result.
#SBATCH --job-name=kon-4669-workers
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=01:10:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=100G
#SBATCH --array=0-3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "4669 Konclude probe failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__kon_4669_worker_probe_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_ARRAY_JOB_ID="${SLURM_ARRAY_JOB_ID:?missing array job identifier}" \
        SLURM_ARRAY_TASK_ID="${SLURM_ARRAY_TASK_ID:?missing array task identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        "${optional_slurm[@]}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|SLURM_ARRAY_TASK_ID|\
        SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 8 ]]
case "$SLURM_ARRAY_TASK_ID" in
    0) workers=1 ;;
    1) workers=2 ;;
    2) workers=4 ;;
    3) workers=8 ;;
    *) echo "invalid array task: $SLURM_ARRAY_TASK_ID" >&2; exit 2 ;;
esac
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]

runner=$submit_dir/reproducible_route_runner.py
runner_sha256=2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6
validator=$submit_dir/validate_documented_route.py
validator_sha256=017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08

konclude_root=$routing_root/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
konclude=$konclude_root/Konclude-build-a
konclude_peer=$konclude_root/Konclude-build-b
konclude_sha256=e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4
konclude_library_dir=$konclude_root/runtime-lib
konclude_runtime_count=33
konclude_runtime_stream_sha256=b26f41184a6a414e13213dbd0059fd8ba49a229f7017f113f5d6bac34ecab123
konclude_build_receipt=$konclude_root/build-receipt.json
konclude_build_receipt_sha256=e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651
konclude_source_manifest_sha256=a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2
konclude_build_driver=$konclude_root/ibex_build_reproducible_konclude.sbatch
konclude_build_driver_sha256=f10514068f31c14da2187f8ebe14dd400f39b36a310a84f6cac811a20d14c6d5
ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1

ontology=$km_root/corpus/ore_ont_4669.owl
ontology_sha256=2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb
run_root=$routing_root/4669-source-konclude-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
result_dir=$run_root/konclude
fingerprint_prefix=$run_root/fingerprint
timeout_s=3600
memory_limit_mb=92160

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

expected_submit_entries=(
    fingerprint_tail_fulliri.py
    ibex_probe_4669_source_konclude_workers.sbatch
    reproducible_route_runner.py
    validate_documented_route.py
    validate_tail_runner.py
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
for pair in \
    "$driver:$driver_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$validator:$validator_sha256" \
    "$konclude:$konclude_sha256" \
    "$konclude_peer:$konclude_sha256" \
    "$konclude_build_receipt:$konclude_build_receipt_sha256" \
    "$konclude_root/source-files.sha256:$konclude_source_manifest_sha256" \
    "$konclude_build_driver:$konclude_build_driver_sha256" \
    "$konclude_root/runtime-files.sha256:$konclude_runtime_stream_sha256" \
    "$ontology:$ontology_sha256" \
    "/usr/bin/ldd:$ldd_sha256" \
    "/usr/bin/python3:$python_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$konclude" "$konclude_peer"
[[ -d $konclude_library_dir && ! -L $konclude_library_dir ]]
[[ $(/usr/bin/find "$konclude_root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$konclude_root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]
[[ ! -e $run_root ]]
/usr/bin/mkdir -p "$result_dir"

/usr/bin/python3 -I - \
    "$submit_dir" "$konclude_build_receipt" \
    "$konclude_build_receipt_sha256" "$konclude_build_driver" \
    "$konclude_build_driver_sha256" "$konclude" "$konclude_sha256" \
    "$konclude_source_manifest_sha256" "$konclude_library_dir" \
    "$konclude_runtime_stream_sha256" "$konclude_runtime_count" \
    "$ldd_sha256" "$run_root/source-runtime.json" <<'PY'
import json
from pathlib import Path
import sys

sys.path.insert(0, sys.argv[1])
from validate_documented_route import (
    konclude_runtime_identity,
    verify_konclude_build_receipt,
)

(
    receipt_path, receipt_sha, driver_path, driver_sha, binary_path,
    binary_sha, source_sha, library_path, runtime_sha, runtime_count,
    ldd_sha, output_path,
) = sys.argv[2:]
receipt, build_checks = verify_konclude_build_receipt(
    receipt_path=Path(receipt_path),
    expected_receipt_sha256=receipt_sha,
    driver=Path(driver_path),
    expected_driver_sha256=driver_sha,
    binary=Path(binary_path),
    expected_binary_sha256=binary_sha,
    expected_source_manifest_sha256=source_sha,
    library_dir=Path(library_path),
    expected_runtime_manifest_sha256=runtime_sha,
    expected_runtime_count=int(runtime_count),
)
runtime = konclude_runtime_identity(
    binary=Path(binary_path),
    library_dir=Path(library_path),
    expected_ldd_sha256=ldd_sha,
)
runtime_checks = {
    "count": runtime["runtime_library_count"] == int(runtime_count),
    "manifest": runtime["runtime_library_manifest_sha256"] == runtime_sha,
    "no_cluster_library": all(
        not entry["path"].startswith("/sw/")
        for entry in runtime["runtime_libraries"]
    ),
}
if not all(build_checks.values()) or not all(runtime_checks.values()):
    raise SystemExit("source build or runtime closure mismatch")
Path(output_path).write_text(
    json.dumps(
        {
            "build_checks": build_checks,
            "build_receipt": receipt,
            "runtime": runtime,
            "runtime_checks": runtime_checks,
        },
        indent=2,
        sort_keys=True,
    ) + "\n",
    encoding="utf-8",
)
PY

runner_environment=(
    PATH=/usr/bin:/bin
    LC_ALL=C
    PYTHONHASHSEED=0
    SLURM_JOB_ID="$SLURM_JOB_ID"
    SLURM_ARRAY_JOB_ID="$SLURM_ARRAY_JOB_ID"
    SLURM_ARRAY_TASK_ID="$SLURM_ARRAY_TASK_ID"
    SLURM_CPUS_PER_TASK="$SLURM_CPUS_PER_TASK"
)
if [[ -n ${SLURM_TMPDIR:-} ]]; then
    runner_environment+=(SLURM_TMPDIR="$SLURM_TMPDIR" TMPDIR="$SLURM_TMPDIR")
fi
set +e
/usr/bin/env -i "${runner_environment[@]}" \
    /usr/bin/python3 -I "$runner" \
        --kind konclude \
        --label "konclude_4669_source_w${workers}" \
        --ontology "$ontology" \
        --binary "$konclude" \
        --output-dir "$result_dir" \
        --timeout "$timeout_s" \
        --memcap-mb "$memory_limit_mb" \
        --workers "$workers" \
        --env "LD_LIBRARY_PATH=$konclude_library_dir"
runner_rc=$?
set -e

primary_output=$(/usr/bin/python3 -I - "$result_dir/run.json" <<'PY'
import json
from pathlib import Path
import sys
run = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
print(run.get("primary_output", ""))
PY
)
fingerprint_rc=1
if [[ $runner_rc -eq 0 && -n $primary_output && -f $primary_output ]]; then
    set +e
    /usr/bin/python3 -I "$fingerprint" \
        --input "$primary_output" \
        --format owlxml \
        --source-ontology "$ontology" \
        --output-prefix "$fingerprint_prefix"
    fingerprint_rc=$?
    set -e
fi

/usr/bin/python3 -I - \
    "$result_dir/run.json" "$fingerprint_prefix.json" "$run_root/PROBE.json" \
    "$runner_rc" "$fingerprint_rc" "$workers" "$timeout_s" \
    "$memory_limit_mb" "$konclude_sha256" "$ontology_sha256" \
    "$konclude_build_receipt_sha256" "$konclude_source_manifest_sha256" \
    "$konclude_runtime_stream_sha256" "$driver_sha256" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

(
    run_text, fingerprint_text, output_text, runner_rc_text,
    fingerprint_rc_text, workers_text, timeout_text, memory_text,
    binary_sha, ontology_sha, receipt_sha, source_sha, runtime_sha,
    driver_sha,
) = sys.argv[1:]
run_path = Path(run_text)
fingerprint_path = Path(fingerprint_text)
run = json.loads(run_path.read_text()) if run_path.is_file() else {}
fingerprint = json.loads(fingerprint_path.read_text()) if fingerprint_path.is_file() else {}
completed = (
    int(runner_rc_text) == 0
    and int(fingerprint_rc_text) == 0
    and run.get("status") == "ok"
    and run.get("return_code") == 0
    and fingerprint.get("status") == "ok"
)
record = {
    "schema_version": 1,
    "status": "source_built_full_iri_reference_ready" if completed else "negative_route_result",
    "reference_ready": completed,
    "workers": int(workers_text),
    "timeout_s": float(timeout_text),
    "memory_limit_mb": int(memory_text),
    "binary_sha256": binary_sha,
    "source_manifest_sha256": source_sha,
    "build_receipt_sha256": receipt_sha,
    "runtime_library_manifest_sha256": runtime_sha,
    "ontology_sha256": ontology_sha,
    "validation_driver_sha256": driver_sha,
    "runner_return_code": int(runner_rc_text),
    "fingerprint_return_code": int(fingerprint_rc_text),
    "run": run,
    "run_record_sha256": hashlib.sha256(run_path.read_bytes()).hexdigest() if run_path.is_file() else "",
    "fingerprint": fingerprint,
}
Path(output_text).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(record, sort_keys=True))
PY

/usr/bin/find "$run_root" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$run_root" -type d -exec /usr/bin/chmod 0555 {} +
