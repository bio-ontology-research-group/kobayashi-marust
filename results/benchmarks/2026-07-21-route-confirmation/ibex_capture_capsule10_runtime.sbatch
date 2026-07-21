#!/bin/bash
# Capture the compute-node dynamic-library closure of the immutable capsule-10
# KM binary. This job verifies but never executes KM.
#SBATCH --job-name=km10-runtime
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "runtime capture failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km10_runtime_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        CAPTURE_ROOT="${CAPTURE_ROOT:?export a new persistent CAPTURE_ROOT}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
if [[ $# -ne 1 || $1 != "$clean_sentinel" ]]; then
    echo "invalid clean-environment sentinel" >&2
    exit 2
fi
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        CAPTURE_ROOT|SLURM_JOB_ID|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ ${SHLVL:-} == 1 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C

capsule=/ibex/scratch/hohndor/km/routing_20260715/reproducible-current-20260721-10-core
candidate=$capsule/km-build-a
peer=$capsule/km-build-b
candidate_sha256=e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30
receipt=$capsule/build-receipt.json
receipt_sha256=c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda
core_file_count=22
core_stream_sha256=59b7aa29a6b0e6fc85c7ecc34fa960395eaa1b258ed5de122433ebfd9167e9de

driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_capture_capsule10_runtime.sbatch
/usr/bin/test -s "$submit_copy"
[[ ! -L $submit_copy ]]
[[ $(/usr/bin/sha256sum "$submit_copy" | /usr/bin/awk '{print $1}') == "$driver_sha256" ]]

[[ $CAPTURE_ROOT == /ibex/scratch/hohndor/km/routing_20260715/runtime-closures/* ]]
[[ ! -e $CAPTURE_ROOT ]]
/usr/bin/mkdir -p "$CAPTURE_ROOT"
/usr/bin/test -x "$candidate"
/usr/bin/test -x "$peer"
/usr/bin/test -s "$receipt"
[[ ! -L $candidate && ! -L $peer && ! -L $receipt ]]
[[ $(/usr/bin/sha256sum "$candidate" | /usr/bin/awk '{print $1}') == "$candidate_sha256" ]]
[[ $(/usr/bin/sha256sum "$peer" | /usr/bin/awk '{print $1}') == "$candidate_sha256" ]]
/usr/bin/cmp -s "$candidate" "$peer"
[[ $(/usr/bin/sha256sum "$receipt" | /usr/bin/awk '{print $1}') == "$receipt_sha256" ]]

expected_capsule_entries=(
    binaries.sha256
    build-a.log
    build-b.log
    build-input-files.sha256
    build-input.tar.gz
    build-receipt.json
    build-receipt.sha256
    build-receipt.stdout.json
    build_reproducible_candidate_on_ws.sh
    cargo-version.txt
    container-os-release.txt
    container-pull.log
    full-test-input-check.log
    full-tests.log
    km-build-a
    km-build-b
    rustc-version.txt
    source-files.sha256
    source-manifest-check.log
    source.tar.gz
    vendor.log
    write_build_receipt.py
)
mapfile -t actual_capsule_entries < <(
    /usr/bin/find "$capsule" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_capsule_entries[@]} -eq ${#expected_capsule_entries[@]} ]]
for index in "${!expected_capsule_entries[@]}"; do
    [[ ${actual_capsule_entries[$index]} == "${expected_capsule_entries[$index]}" ]]
done
for entry in "${expected_capsule_entries[@]}"; do
    [[ -f $capsule/$entry && ! -L $capsule/$entry ]]
done

(
    cd "$capsule"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z \
        | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$CAPTURE_ROOT/capsule-files.sha256"
[[ $(/usr/bin/wc -l < "$CAPTURE_ROOT/capsule-files.sha256") -eq "$core_file_count" ]]
[[ $(/usr/bin/sha256sum "$CAPTURE_ROOT/capsule-files.sha256" | /usr/bin/awk '{print $1}') == "$core_stream_sha256" ]]

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/ldd "$candidate" \
    > "$CAPTURE_ROOT/ldd.stdout" 2> "$CAPTURE_ROOT/ldd.stderr"
/usr/bin/awk '$2 == "=>" && $3 == "not" { print }' \
    "$CAPTURE_ROOT/ldd.stdout" > "$CAPTURE_ROOT/unresolved.txt"
[[ ! -s $CAPTURE_ROOT/unresolved.txt ]]
/usr/bin/awk '
    $2 == "=>" && substr($3, 1, 1) == "/" { print $3; next }
    substr($1, 1, 1) == "/" { print $1 }
' "$CAPTURE_ROOT/ldd.stdout" | /usr/bin/sort -u \
    > "$CAPTURE_ROOT/runtime-paths.txt"
[[ -s $CAPTURE_ROOT/runtime-paths.txt ]]
while IFS= read -r library; do
    /usr/bin/test -f "$library"
    /usr/bin/sha256sum "$library"
done < "$CAPTURE_ROOT/runtime-paths.txt" \
    > "$CAPTURE_ROOT/runtime-files.sha256"

ldd_resolved=$(/usr/bin/readlink -f /usr/bin/ldd)
python_resolved=$(/usr/bin/readlink -f /usr/bin/python3)
{
    /usr/bin/printf 'field\tvalue\n'
    /usr/bin/printf 'status\tcaptured_for_later_independent_recheck\n'
    /usr/bin/printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
    /usr/bin/printf 'host\t%s\n' "$(/usr/bin/hostname)"
    /usr/bin/printf 'driver\t%s\n' "$driver"
    /usr/bin/printf 'driver_sha256\t%s\n' "$driver_sha256"
    /usr/bin/printf 'capsule\t%s\n' "$capsule"
    /usr/bin/printf 'capsule_stream_sha256\t%s\n' "$core_stream_sha256"
    /usr/bin/printf 'binary_sha256\t%s\n' "$candidate_sha256"
    /usr/bin/printf 'build_receipt_sha256\t%s\n' "$receipt_sha256"
    /usr/bin/printf 'ldd_requested\t/usr/bin/ldd\n'
    /usr/bin/printf 'ldd_resolved\t%s\n' "$ldd_resolved"
    /usr/bin/printf 'ldd_sha256\t%s\n' "$(/usr/bin/sha256sum /usr/bin/ldd | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'python_resolved\t%s\n' "$python_resolved"
    /usr/bin/printf 'python_sha256\t%s\n' "$(/usr/bin/sha256sum "$python_resolved" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'runtime_library_count\t%s\n' "$(/usr/bin/wc -l < "$CAPTURE_ROOT/runtime-files.sha256")"
    /usr/bin/printf 'runtime_library_manifest_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/runtime-files.sha256" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stdout_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/ldd.stdout" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stderr_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/ldd.stderr" | /usr/bin/awk '{print $1}')"
} > "$CAPTURE_ROOT/SUMMARY.tsv"

/usr/bin/chmod a-w "$CAPTURE_ROOT"/*
/usr/bin/chmod a-w "$CAPTURE_ROOT"
/usr/bin/cat "$CAPTURE_ROOT/SUMMARY.tsv"


