#!/bin/bash
# Reproduce capsule-10's ORE 4669 ht_bridge output under the ORE limits.
# This is candidate evidence only. It does not claim correctness without an
# independent complete oracle.
#SBATCH --job-name=km-4669-cap10
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "4669 candidate capture failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_4669_candidate10_env_i_v1__
if [[ $# -eq 0 ]]; then
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
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|SLURM_TMPDIR|\
        PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
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
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6
validator=$submit_dir/validate_documented_route.py
validator_sha256=017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08

capsule=$routing_root/reproducible-current-20260721-10-core
binary=$capsule/km-build-a
binary_peer=$capsule/km-build-b
binary_sha256=e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30
source_manifest_sha256=4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda
km_runtime_count=6
km_runtime_stream_sha256=ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5
ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1

ontology=$km_root/corpus/ore_ont_4669.owl
ontology_sha256=2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb
run_root=$routing_root/4669-candidate10-$SLURM_JOB_ID
result_dir=$run_root/km
fingerprint_prefix=$run_root/fingerprint

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

expected_submit_entries=(
    fingerprint_tail_fulliri.py
    ibex_capture_4669_candidate10.sbatch
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
    "$binary:$binary_sha256" \
    "$binary_peer:$binary_sha256" \
    "$capsule/source-files.sha256:$source_manifest_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$ontology:$ontology_sha256" \
    "/usr/bin/ldd:$ldd_sha256" \
    "/usr/bin/python3:$python_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$binary" "$binary_peer"
[[ ! -e $run_root ]]
/usr/bin/mkdir -p "$result_dir"

/usr/bin/python3 -I - \
    "$submit_dir" "$binary" "$ldd_sha256" "$km_runtime_count" \
    "$km_runtime_stream_sha256" "$run_root/runtime-identity.json" <<'PY'
import json
from pathlib import Path
import sys

sys.path.insert(0, sys.argv[1])
from validate_documented_route import executable_runtime_identity

identity = executable_runtime_identity(
    binary=Path(sys.argv[2]),
    environment={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
    expected_ldd_sha256=sys.argv[3],
)
checks = {
    "runtime_count": identity["runtime_library_count"] == int(sys.argv[4]),
    "runtime_manifest": identity["runtime_library_manifest_sha256"] == sys.argv[5],
}
if not all(checks.values()):
    raise SystemExit(f"KM runtime closure mismatch: {checks}")
Path(sys.argv[6]).write_text(
    json.dumps({"checks": checks, "identity": identity}, indent=2, sort_keys=True)
    + "\n",
    encoding="utf-8",
)
PY

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
/usr/bin/env -i "${runner_environment[@]}" \
    /usr/bin/python3 -I "$runner" \
        --kind km \
        --label km_4669_capsule10_ht_bridge \
        --ontology "$ontology" \
        --binary "$binary" \
        --output-dir "$result_dir" \
        --timeout 240 \
        --memcap-mb 20480 \
        --workers 16 \
        --env KM_ROUTE=ht_bridge \
        --env KM_TIMING=1
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
        --format json \
        --source-ontology "$ontology" \
        --output-prefix "$fingerprint_prefix"
    fingerprint_rc=$?
    set -e
fi

/usr/bin/python3 -I - \
    "$result_dir/run.json" "$result_dir/launcher.json" \
    "$result_dir/stderr.log" "$fingerprint_prefix.json" \
    "$run_root/CANDIDATE.json" "$runner_rc" "$fingerprint_rc" \
    "$binary" "$binary_sha256" "$ontology" "$ontology_sha256" \
    "$source_manifest_sha256" "$build_receipt_sha256" \
    "$km_runtime_stream_sha256" "$driver_sha256" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import sys

(
    run_text, launcher_text, stderr_text, fingerprint_text, output_text,
    runner_rc_text, fingerprint_rc_text, binary, binary_sha, ontology,
    ontology_sha, source_sha, receipt_sha, runtime_sha, driver_sha,
) = sys.argv[1:]
run_path = Path(run_text)
launcher_path = Path(launcher_text)
stderr_path = Path(stderr_text)
fingerprint_path = Path(fingerprint_text)
run = json.loads(run_path.read_text()) if run_path.is_file() else {}
launcher = json.loads(launcher_path.read_text()) if launcher_path.is_file() else {}
fingerprint = json.loads(fingerprint_path.read_text()) if fingerprint_path.is_file() else {}
traces = re.findall(
    r"KM_TIMING frontend done[^\n]* route=([a-z0-9_]+)",
    stderr_path.read_text(encoding="utf-8", errors="replace")
    if stderr_path.is_file() else "",
)
checks = {
    "runner_exit_zero": int(runner_rc_text) == 0,
    "fingerprint_exit_zero": int(fingerprint_rc_text) == 0,
    "run_ok": run.get("status") == "ok" and run.get("return_code") == 0,
    "binary": run.get("binary") == binary and run.get("binary_sha256") == binary_sha,
    "ontology": run.get("ontology") == ontology and run.get("ontology_sha256") == ontology_sha,
    "limits": run.get("timeout_s") == 240.0 and run.get("memory_limit_mb") == 20480 and float(run.get("wall_s", 241)) <= 240.5 and float(run.get("peak_mb", 20481)) <= 20480,
    "cpus": run.get("cpus") == 16,
    "semantic_environment": run.get("environment") == {"KM_ROUTE": "ht_bridge", "KM_TIMING": "1"},
    "exact_command": run.get("command") == [binary, "classify", ontology],
    "launcher": launcher.get("status") == "verified" and all((launcher.get("checks") or {}).values()),
    "route_trace": traces == ["ht_bridge"],
    "fingerprint": fingerprint.get("status") == "ok",
}
record = {
    "schema_version": 1,
    "status": "candidate_reproduced_unadjudicated" if all(checks.values()) else "rejected",
    "correctness_claim": False,
    "reason": "No complete independent 4669 oracle has passed yet.",
    "checks": checks,
    "route": "ht_bridge",
    "route_trace": traces,
    "binary_sha256": binary_sha,
    "source_manifest_sha256": source_sha,
    "build_receipt_sha256": receipt_sha,
    "runtime_library_manifest_sha256": runtime_sha,
    "ontology_sha256": ontology_sha,
    "validation_driver_sha256": driver_sha,
    "run_record": str(run_path),
    "run_record_sha256": hashlib.sha256(run_path.read_bytes()).hexdigest() if run_path.is_file() else "",
    "fingerprint": fingerprint,
}
Path(output_text).write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(record, sort_keys=True))
raise SystemExit(0 if record["status"] == "candidate_reproduced_unadjudicated" else 1)
PY

/usr/bin/find "$run_root" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$run_root" -type d -exec /usr/bin/chmod 0555 {} +
