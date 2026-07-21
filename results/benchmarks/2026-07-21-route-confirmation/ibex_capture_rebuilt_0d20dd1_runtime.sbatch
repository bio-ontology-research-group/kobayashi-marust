#!/bin/bash
# Capture the compute-node runtime closure of the twice-built 0d20dd1 KM
# capsule. This verifies the executable and its test receipt but never runs KM.
#SBATCH --job-name=km0d-runtime
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "runtime capture failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_0d20dd1_runtime_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        CAPTURE_ROOT="${CAPTURE_ROOT:?export a new persistent CAPTURE_ROOT}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        CAPTURE_ROOT|SLURM_JOB_ID|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
export PATH=/usr/bin:/bin
export LC_ALL=C

root=/ibex/scratch/hohndor/km/routing_20260715/reproducible-0d20dd1-20260721-01
capsule=$root/capsule
tests=$root/tests
candidate=$capsule/km-build-a
peer=$capsule/km-build-b
candidate_sha256=ced4544f50a988f7a07059195ce38a6fca65f0692998c31dce656f513ad66a57
receipt=$capsule/build-receipt.json
receipt_sha256=9a6eb331df6b86710862eef62878df082f9160f04104a242580d132ef2434ed1
source_manifest_sha256=f6b393cbda6448ccd255f1b109385134eed8b441439826b70b2e1ccd0a169537
test_receipt=$tests/test-receipt.json
test_receipt_sha256=bac2429376aad6ff2409f55b9af6a52ef162e2e6dc5fb0c48c7c6df52111d006
capsule_file_count=20
capsule_stream_sha256=fd2a9a586a178f2b5bcc2acfd68c00581a0e4037a758f45eebeaac535be6ca37
test_file_count=4
test_stream_sha256=7ef299a36f727e3bfb14a142d7b5d21e0bb5a1987e3da9100e1cc0c86de5addf

driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_capture_rebuilt_0d20dd1_runtime.sbatch
[[ -s $submit_copy && ! -L $submit_copy ]]
[[ $(/usr/bin/sha256sum "$submit_copy" | /usr/bin/awk '{print $1}') == "$driver_sha256" ]]

[[ $CAPTURE_ROOT == /ibex/scratch/hohndor/km/routing_20260715/runtime-closures/* ]]
[[ ! -e $CAPTURE_ROOT ]]
[[ -d $root && -d $capsule && -d $tests ]]
[[ $(/usr/bin/find "$root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/sha256sum "$candidate" | /usr/bin/awk '{print $1}') == "$candidate_sha256" ]]
[[ $(/usr/bin/sha256sum "$peer" | /usr/bin/awk '{print $1}') == "$candidate_sha256" ]]
/usr/bin/cmp -s "$candidate" "$peer"
[[ $(/usr/bin/sha256sum "$receipt" | /usr/bin/awk '{print $1}') == "$receipt_sha256" ]]
[[ $(/usr/bin/sha256sum "$capsule/source-files.sha256" | /usr/bin/awk '{print $1}') == "$source_manifest_sha256" ]]
[[ $(/usr/bin/sha256sum "$test_receipt" | /usr/bin/awk '{print $1}') == "$test_receipt_sha256" ]]

/usr/bin/mkdir "$CAPTURE_ROOT"
(
    cd "$capsule"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$CAPTURE_ROOT/capsule-files.sha256"
(
    cd "$tests"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$CAPTURE_ROOT/test-files.sha256"
[[ $(/usr/bin/wc -l < "$CAPTURE_ROOT/capsule-files.sha256") -eq $capsule_file_count ]]
[[ $(/usr/bin/wc -l < "$CAPTURE_ROOT/test-files.sha256") -eq $test_file_count ]]
[[ $(/usr/bin/sha256sum "$CAPTURE_ROOT/capsule-files.sha256" | /usr/bin/awk '{print $1}') == "$capsule_stream_sha256" ]]
[[ $(/usr/bin/sha256sum "$CAPTURE_ROOT/test-files.sha256" | /usr/bin/awk '{print $1}') == "$test_stream_sha256" ]]

/usr/bin/python3 -I - "$receipt" "$test_receipt" \
    "$candidate_sha256" "$source_manifest_sha256" "$receipt_sha256" <<'PY'
import json
from pathlib import Path
import sys

build = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
tests = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
assert build.get("status") == "verified_reproducible"
assert build.get("outputs", {}).get("byte_identical") is True
assert build.get("outputs", {}).get("build_a_sha256") == sys.argv[3]
assert build.get("outputs", {}).get("build_b_sha256") == sys.argv[3]
assert build.get("source", {}).get("manifest_sha256") == sys.argv[4]
assert tests.get("status") == "verified_full_tests"
assert tests.get("failed") == 0 and tests.get("passed") == 1390
assert tests.get("capsule_build_receipt_sha256") == sys.argv[5]
PY

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

{
    /usr/bin/printf 'field\tvalue\n'
    /usr/bin/printf 'status\tcaptured_for_later_independent_recheck\n'
    /usr/bin/printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
    /usr/bin/printf 'host\t%s\n' "$(/usr/bin/hostname)"
    /usr/bin/printf 'driver_sha256\t%s\n' "$driver_sha256"
    /usr/bin/printf 'source_commit\t0d20dd13312c16dec4ff256852979fb4c927556a\n'
    /usr/bin/printf 'capsule_stream_sha256\t%s\n' "$capsule_stream_sha256"
    /usr/bin/printf 'test_stream_sha256\t%s\n' "$test_stream_sha256"
    /usr/bin/printf 'binary_sha256\t%s\n' "$candidate_sha256"
    /usr/bin/printf 'build_receipt_sha256\t%s\n' "$receipt_sha256"
    /usr/bin/printf 'source_manifest_sha256\t%s\n' "$source_manifest_sha256"
    /usr/bin/printf 'test_receipt_sha256\t%s\n' "$test_receipt_sha256"
    /usr/bin/printf 'ldd_sha256\t%s\n' "$(/usr/bin/sha256sum /usr/bin/ldd | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'runtime_library_count\t%s\n' "$(/usr/bin/wc -l < "$CAPTURE_ROOT/runtime-files.sha256")"
    /usr/bin/printf 'runtime_library_manifest_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/runtime-files.sha256" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stdout_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/ldd.stdout" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stderr_sha256\t%s\n' "$(/usr/bin/sha256sum "$CAPTURE_ROOT/ldd.stderr" | /usr/bin/awk '{print $1}')"
} > "$CAPTURE_ROOT/SUMMARY.tsv"

/usr/bin/chmod a-w "$CAPTURE_ROOT"/*
/usr/bin/chmod a-w "$CAPTURE_ROOT"
/usr/bin/cat "$CAPTURE_ROOT/SUMMARY.tsv"
