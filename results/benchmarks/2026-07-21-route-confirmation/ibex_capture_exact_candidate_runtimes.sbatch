#!/bin/bash
# Capture, without executing KM, the compute-node runtime closures for three
# exact-source historical candidate capsules.
#SBATCH --job-name=km-exact-runtime
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --array=0-2%3
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "exact candidate runtime capture failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_exact_candidate_runtime_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        RUNTIME_ROOT="${RUNTIME_ROOT:?export a new persistent RUNTIME_ROOT}" \
        CAPSULE_REGISTRY="${CAPSULE_REGISTRY:?export the base capsule registry}" \
        CAPSULE_REGISTRY_SHA256="${CAPSULE_REGISTRY_SHA256:?export its SHA-256}" \
        CAPSULE_REGISTRY_RECEIPT="${CAPSULE_REGISTRY_RECEIPT:?export its receipt}" \
        CAPSULE_REGISTRY_RECEIPT_SHA256="${CAPSULE_REGISTRY_RECEIPT_SHA256:?export the receipt SHA-256}" \
        CAPSULE_GENERATOR_SHA256="${CAPSULE_GENERATOR_SHA256:?export the generator SHA-256}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_ARRAY_JOB_ID="${SLURM_ARRAY_JOB_ID:?missing array job identifier}" \
        SLURM_ARRAY_TASK_ID="${SLURM_ARRAY_TASK_ID:?missing array task identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        RUNTIME_ROOT|CAPSULE_REGISTRY|CAPSULE_REGISTRY_SHA256|\
        CAPSULE_REGISTRY_RECEIPT|CAPSULE_REGISTRY_RECEIPT_SHA256|\
        CAPSULE_GENERATOR_SHA256|SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|\
        SLURM_ARRAY_TASK_ID|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_ARRAY_TASK_ID -ge 0 && $SLURM_ARRAY_TASK_ID -le 2 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C

driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_capture_exact_candidate_runtimes.sbatch
[[ -s $submit_copy && ! -L $submit_copy ]]
[[ $(/usr/bin/sha256sum "$submit_copy" | /usr/bin/awk '{print $1}') == "$driver_sha256" ]]

registry=$(/usr/bin/readlink -f "$CAPSULE_REGISTRY")
registry_receipt=$(/usr/bin/readlink -f "$CAPSULE_REGISTRY_RECEIPT")
[[ -s $registry && ! -L $registry ]]
[[ -s $registry_receipt && ! -L $registry_receipt ]]
[[ $(/usr/bin/sha256sum "$registry" | /usr/bin/awk '{print $1}') == "$CAPSULE_REGISTRY_SHA256" ]]
[[ $(/usr/bin/sha256sum "$registry_receipt" | /usr/bin/awk '{print $1}') == "$CAPSULE_REGISTRY_RECEIPT_SHA256" ]]

/usr/bin/python3 -I - "$registry_receipt" "$CAPSULE_REGISTRY_SHA256" \
    "$CAPSULE_GENERATOR_SHA256" <<'PY'
import json
from pathlib import Path
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
checks = receipt.get("checks") or {}
expected = {
    "status": "source_bound_exact_candidate_capsules",
    "rows": 3,
    "output_sha256": sys.argv[2],
    "generator_sha256": sys.argv[3],
    "expected_source_verifier_sha256": "a5907b0af2b00d7b530edf0148a3c0aaa1016fe4d96554be2582ea31ce2f3148",
}
failures = [key for key, value in expected.items() if receipt.get(key) != value]
if (
    failures
    or len(checks) != 3
    or any(not value or not all(value.values()) for value in checks.values())
):
    raise SystemExit(f"base capsule registry receipt failed: {failures}")
PY

mapfile -d '' -t metadata < <(
    /usr/bin/python3 -I - "$registry" "$SLURM_ARRAY_TASK_ID" <<'PY'
import csv
from pathlib import Path
import sys

with Path(sys.argv[1]).open(newline="", encoding="utf-8") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))
index = int(sys.argv[2])
if len(rows) != 3 or index not in range(3):
    raise SystemExit("capsule registry has an unexpected shape")
keys = (
    "candidate", "commit", "binary", "peer_binary", "binary_sha256",
    "source_manifest_sha256", "build_receipt", "build_receipt_sha256",
    "test_receipt", "test_receipt_sha256", "passed_tests",
    "source_identity", "source_identity_sha256",
)
for key in keys:
    value = rows[index].get(key, "")
    if not value or "\0" in value or "\n" in value:
        raise SystemExit(f"invalid capsule field: {key}")
    sys.stdout.write(value + "\0")
PY
)
[[ ${#metadata[@]} -eq 13 ]]
candidate=${metadata[0]}
source_commit=${metadata[1]}
binary=${metadata[2]}
peer=${metadata[3]}
binary_sha256=${metadata[4]}
source_manifest_sha256=${metadata[5]}
build_receipt=${metadata[6]}
build_receipt_sha256=${metadata[7]}
test_receipt=${metadata[8]}
test_receipt_sha256=${metadata[9]}
passed_tests=${metadata[10]}
source_identity=${metadata[11]}
source_identity_sha256=${metadata[12]}

case "$candidate" in
    a639ab5|a068059|a0d0148816c5) ;;
    *) echo "unexpected candidate label: $candidate" >&2; exit 2 ;;
esac
for path in "$binary" "$peer" "$build_receipt" "$test_receipt" \
    "$source_identity"; do
    [[ -s $path && ! -L $path ]]
done
capsule_dir=$(/usr/bin/dirname "$binary")
source_manifest=$capsule_dir/source-files.sha256
[[ -s $source_manifest && ! -L $source_manifest ]]
[[ $(/usr/bin/sha256sum "$binary" | /usr/bin/awk '{print $1}') == "$binary_sha256" ]]
[[ $(/usr/bin/sha256sum "$peer" | /usr/bin/awk '{print $1}') == "$binary_sha256" ]]
/usr/bin/cmp -s "$binary" "$peer"
[[ $(/usr/bin/sha256sum "$source_manifest" | /usr/bin/awk '{print $1}') == "$source_manifest_sha256" ]]
[[ $(/usr/bin/sha256sum "$build_receipt" | /usr/bin/awk '{print $1}') == "$build_receipt_sha256" ]]
[[ $(/usr/bin/sha256sum "$test_receipt" | /usr/bin/awk '{print $1}') == "$test_receipt_sha256" ]]
[[ $(/usr/bin/sha256sum "$source_identity" | /usr/bin/awk '{print $1}') == "$source_identity_sha256" ]]

/usr/bin/python3 -I - "$build_receipt" "$test_receipt" "$source_identity" \
    "$source_commit" "$binary_sha256" "$source_manifest_sha256" \
    "$build_receipt_sha256" "$passed_tests" <<'PY'
import json
from pathlib import Path
import sys

build = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
tests = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
identity = json.loads(Path(sys.argv[3]).read_text(encoding="utf-8"))
expected_commit, binary, source, build_sha, passed = sys.argv[4:]
checks = {
    "build_verified": build.get("status") == "verified_reproducible",
    "build_identical": (build.get("outputs") or {}).get("byte_identical") is True,
    "build_a": (build.get("outputs") or {}).get("build_a_sha256") == binary,
    "build_b": (build.get("outputs") or {}).get("build_b_sha256") == binary,
    "build_source": (build.get("source") or {}).get("manifest_sha256") == source,
    "tests_verified": tests.get("status") == "verified_full_tests",
    "tests_pass": tests.get("failed") == 0
        and tests.get("return_code") == 0
        and tests.get("passed") == int(passed),
    "tests_bind_build": tests.get("capsule_build_receipt_sha256") == build_sha,
    "identity_verified": identity.get("status") == "verified_exact_git_source",
    "identity_commit": identity.get("commit") == expected_commit,
    "identity_source": identity.get("source_manifest_sha256") == source,
    "identity_build": identity.get("build_receipt_sha256") == build_sha,
}
if not all(checks.values()):
    raise SystemExit([key for key, value in checks.items() if not value])
PY

[[ $RUNTIME_ROOT == /ibex/scratch/hohndor/km/routing_20260715/runtime-closures/* ]]
/usr/bin/mkdir -p "$RUNTIME_ROOT"
capture_root=$RUNTIME_ROOT/exact-candidate-${candidate}-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
[[ ! -e $capture_root ]]
/usr/bin/mkdir "$capture_root"

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/ldd "$binary" \
    > "$capture_root/ldd.stdout" 2> "$capture_root/ldd.stderr"
/usr/bin/awk '$2 == "=>" && $3 == "not" { print }' \
    "$capture_root/ldd.stdout" > "$capture_root/unresolved.txt"
[[ ! -s $capture_root/unresolved.txt ]]
/usr/bin/awk '
    $2 == "=>" && substr($3, 1, 1) == "/" { print $3; next }
    substr($1, 1, 1) == "/" { print $1 }
' "$capture_root/ldd.stdout" | /usr/bin/sort -u \
    > "$capture_root/runtime-paths.txt"
[[ -s $capture_root/runtime-paths.txt ]]
while IFS= read -r library; do
    /usr/bin/test -f "$library"
    /usr/bin/sha256sum "$library"
done < "$capture_root/runtime-paths.txt" \
    > "$capture_root/runtime-files.sha256"

{
    /usr/bin/printf 'field\tvalue\n'
    /usr/bin/printf 'status\tcaptured_for_later_independent_recheck\n'
    /usr/bin/printf 'candidate\t%s\n' "$candidate"
    /usr/bin/printf 'source_commit\t%s\n' "$source_commit"
    /usr/bin/printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
    /usr/bin/printf 'slurm_array_job_id\t%s\n' "$SLURM_ARRAY_JOB_ID"
    /usr/bin/printf 'slurm_array_task_id\t%s\n' "$SLURM_ARRAY_TASK_ID"
    /usr/bin/printf 'host\t%s\n' "$(/usr/bin/hostname)"
    /usr/bin/printf 'driver_sha256\t%s\n' "$driver_sha256"
    /usr/bin/printf 'capsule_registry_sha256\t%s\n' "$CAPSULE_REGISTRY_SHA256"
    /usr/bin/printf 'capsule_registry_receipt_sha256\t%s\n' "$CAPSULE_REGISTRY_RECEIPT_SHA256"
    /usr/bin/printf 'binary_sha256\t%s\n' "$binary_sha256"
    /usr/bin/printf 'source_manifest_sha256\t%s\n' "$source_manifest_sha256"
    /usr/bin/printf 'build_receipt_sha256\t%s\n' "$build_receipt_sha256"
    /usr/bin/printf 'test_receipt_sha256\t%s\n' "$test_receipt_sha256"
    /usr/bin/printf 'source_identity_sha256\t%s\n' "$source_identity_sha256"
    /usr/bin/printf 'ldd_sha256\t%s\n' "$(/usr/bin/sha256sum /usr/bin/ldd | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'runtime_library_count\t%s\n' "$(/usr/bin/wc -l < "$capture_root/runtime-files.sha256")"
    /usr/bin/printf 'runtime_library_manifest_sha256\t%s\n' "$(/usr/bin/sha256sum "$capture_root/runtime-files.sha256" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stdout_sha256\t%s\n' "$(/usr/bin/sha256sum "$capture_root/ldd.stdout" | /usr/bin/awk '{print $1}')"
    /usr/bin/printf 'ldd_stderr_sha256\t%s\n' "$(/usr/bin/sha256sum "$capture_root/ldd.stderr" | /usr/bin/awk '{print $1}')"
} > "$capture_root/SUMMARY.tsv"

/usr/bin/chmod a-w "$capture_root"/*
/usr/bin/chmod a-w "$capture_root"
/usr/bin/cat "$capture_root/SUMMARY.tsv"
