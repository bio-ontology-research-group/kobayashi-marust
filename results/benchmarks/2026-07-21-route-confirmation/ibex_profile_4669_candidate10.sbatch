#!/bin/bash
# Instrument capsule-10's exact 4669 ht_bridge route without changing its
# semantic settings. The record is diagnostic and cannot establish correctness.
#SBATCH --job-name=km-4669-profile
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "4669 profile failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_4669_profile_env_i_v1__
if [[ ${1:-} != "$clean_sentinel" ]]; then
    profile_mode=${1:-sparse}
    [[ $profile_mode == sparse || $profile_mode == p-only ]]
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        "${optional_slurm[@]}" \
        /bin/bash "$script_path" "$clean_sentinel" "$profile_mode"
fi
[[ $# -eq 2 && $1 == "$clean_sentinel" ]]
profile_mode=$2
[[ $profile_mode == sparse || $profile_mode == p-only ]]
shift 2
[[ $SLURM_CPUS_PER_TASK == 16 ]]
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
binary=$routing_root/reproducible-current-20260721-10-core/km-build-a
binary_peer=$routing_root/reproducible-current-20260721-10-core/km-build-b
binary_sha256=e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30
build_receipt=$routing_root/reproducible-current-20260721-10-core/build-receipt.json
build_receipt_sha256=c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda
ontology=$km_root/corpus/ore_ont_4669.owl
ontology_sha256=2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb
run_root=$routing_root/4669-profile10-$profile_mode-$SLURM_JOB_ID

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}
expected_submit_entries=(
    ibex_profile_4669_candidate10.sbatch
    reproducible_route_runner.py
    validate_tail_runner.py
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
for pair in \
    "$driver:$driver_sha256" "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" "$binary:$binary_sha256" \
    "$binary_peer:$binary_sha256" "$build_receipt:$build_receipt_sha256" \
    "$ontology:$ontology_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -s $path && $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$binary" "$binary_peer"
[[ ! -e $run_root ]]
/usr/bin/mkdir -p "$run_root/km"

runner_environment=(
    PATH=/usr/bin:/bin
    LC_ALL=C
    PYTHONHASHSEED=0
    SLURM_JOB_ID="$SLURM_JOB_ID"
    SLURM_CPUS_PER_TASK="$SLURM_CPUS_PER_TASK"
)
if [[ -n ${SLURM_TMPDIR:-} ]]; then
    runner_environment+=(SLURM_TMPDIR="$SLURM_TMPDIR" TMPDIR="$SLURM_TMPDIR")
fi
set +e
profile_environment=(
    --env KM_ROUTE=ht_bridge
    --env KM_TIMING=1
    --env KM_BRIDGE_PROGRESS=1
    --env KM_NEG_EXIST_PROFILE_PROGRESS=1
    --env KM_BRIDGE_PHASES=1
)
if [[ $profile_mode == p-only ]]; then
    profile_environment+=(--env KM_NEG_EXIST_PROXY_P_ONLY=1)
fi
/usr/bin/env -i "${runner_environment[@]}" \
    /usr/bin/python3 -I "$runner" \
        --kind km --label "km_4669_capsule10_profile_$profile_mode" \
        --ontology "$ontology" --binary "$binary" \
        --output-dir "$run_root/km" --timeout 240 --memcap-mb 20480 \
        --workers 16 \
        "${profile_environment[@]}"
runner_rc=$?
set -e

/usr/bin/python3 -I - \
    "$run_root/km/run.json" "$run_root/km/stderr.log" \
    "$run_root/PROFILE.json" "$runner_rc" "$driver_sha256" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

run_path, stderr_path, output_path = map(Path, sys.argv[1:4])
run = json.loads(run_path.read_text()) if run_path.is_file() else {}
stderr = stderr_path.read_bytes() if stderr_path.is_file() else b""
record = {
    "schema_version": 1,
    "status": "diagnostic_complete",
    "correctness_claim": False,
    "runner_return_code": int(sys.argv[4]),
    "validation_driver_sha256": sys.argv[5],
    "run": run,
    "run_record_sha256": hashlib.sha256(run_path.read_bytes()).hexdigest()
    if run_path.is_file() else "",
    "stderr_bytes": len(stderr),
    "stderr_lines": stderr.count(b"\n"),
    "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
}
output_path.write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(record, sort_keys=True))
PY
/usr/bin/find "$run_root" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$run_root" -type d -exec /usr/bin/chmod 0555 {} +
