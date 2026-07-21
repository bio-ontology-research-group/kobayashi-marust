#!/bin/bash
# Replay five historical production_all routes with binaries rebuilt twice
# from their exact Git commits. Historical executables are provenance only.
#SBATCH --job-name=km-exact-routes
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:38:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-4%5
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "exact candidate route replay failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_exact_candidate_replay_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        REPLAY_REGISTRY="${REPLAY_REGISTRY:?export the five-row replay registry}" \
        REPLAY_REGISTRY_SHA256="${REPLAY_REGISTRY_SHA256:?export its SHA-256}" \
        REPLAY_REGISTRY_RECEIPT="${REPLAY_REGISTRY_RECEIPT:?export its receipt}" \
        REPLAY_REGISTRY_RECEIPT_SHA256="${REPLAY_REGISTRY_RECEIPT_SHA256:?export the receipt SHA-256}" \
        CAPSULE_REGISTRY="${CAPSULE_REGISTRY:?export the final capsule registry}" \
        CAPSULE_REGISTRY_SHA256="${CAPSULE_REGISTRY_SHA256:?export its SHA-256}" \
        CAPSULE_REGISTRY_RECEIPT="${CAPSULE_REGISTRY_RECEIPT:?export its receipt}" \
        CAPSULE_REGISTRY_RECEIPT_SHA256="${CAPSULE_REGISTRY_RECEIPT_SHA256:?export the receipt SHA-256}" \
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
        REPLAY_REGISTRY|REPLAY_REGISTRY_SHA256|REPLAY_REGISTRY_RECEIPT|\
        REPLAY_REGISTRY_RECEIPT_SHA256|CAPSULE_REGISTRY|\
        CAPSULE_REGISTRY_SHA256|CAPSULE_REGISTRY_RECEIPT|\
        CAPSULE_REGISTRY_RECEIPT_SHA256|SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|\
        SLURM_ARRAY_TASK_ID|SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|\
        SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 16 ]]
[[ $SLURM_ARRAY_TASK_ID -ge 0 && $SLURM_ARRAY_TASK_ID -le 4 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
validation_driver=$submit_dir/ibex_confirm_exact_candidate_routes.sbatch
validator=$submit_dir/validate_documented_route.py
validator_sha256=f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc
runner=$submit_dir/reproducible_route_runner.py
runner_sha256=2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6
replay_generator_sha256=15b7a4ba62c730ffde57f79783c66bce6da7f5b43dd77998742e58970942230c
capsule_generator_sha256=729212823439e0fb39f66ebd9ed0522672c9df52a6a8eadd5c0bd64169d8d07b
runtime_driver_sha256=c619a815cc9667fd8c63236c3f33ac7a8c78290a65f4036e2acb235ed3fe0f90

expected_submit_entries=(
    fingerprint_tail_fulliri.py
    ibex_confirm_exact_candidate_routes.sbatch
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
    "$validation_driver:$driver_sha256" \
    "$validator:$validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -s $path && ! -L $path ]]
    [[ $(/usr/bin/sha256sum "$path" | /usr/bin/awk '{print $1}') == "$expected" ]]
done

registry=$(/usr/bin/readlink -f "$REPLAY_REGISTRY")
registry_receipt=$(/usr/bin/readlink -f "$REPLAY_REGISTRY_RECEIPT")
capsules=$(/usr/bin/readlink -f "$CAPSULE_REGISTRY")
capsules_receipt=$(/usr/bin/readlink -f "$CAPSULE_REGISTRY_RECEIPT")
for path in "$registry" "$registry_receipt" "$capsules" \
    "$capsules_receipt"; do
    [[ -s $path && ! -L $path ]]
done
[[ $(/usr/bin/sha256sum "$registry" | /usr/bin/awk '{print $1}') == "$REPLAY_REGISTRY_SHA256" ]]
[[ $(/usr/bin/sha256sum "$registry_receipt" | /usr/bin/awk '{print $1}') == "$REPLAY_REGISTRY_RECEIPT_SHA256" ]]
[[ $(/usr/bin/sha256sum "$capsules" | /usr/bin/awk '{print $1}') == "$CAPSULE_REGISTRY_SHA256" ]]
[[ $(/usr/bin/sha256sum "$capsules_receipt" | /usr/bin/awk '{print $1}') == "$CAPSULE_REGISTRY_RECEIPT_SHA256" ]]

/usr/bin/python3 -I - "$registry_receipt" "$capsules_receipt" \
    "$REPLAY_REGISTRY_SHA256" "$CAPSULE_REGISTRY_SHA256" \
    "$replay_generator_sha256" "$capsule_generator_sha256" \
    "$runtime_driver_sha256" <<'PY'
import json
from pathlib import Path
import sys

replay = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
capsules = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
expected_replay = {
    "status": "source_bound_exact_candidate_replay_registry",
    "rows": 5,
    "output_sha256": sys.argv[3],
    "candidate_capsules_sha256": sys.argv[4],
    "generator_sha256": sys.argv[5],
    "selected_registry_sha256": "9515703a4343782ebcae3ba414390a1b063f91c0e119af412bdbad0b56ddd72b",
}
expected_capsules = {
    "status": "source_bound_exact_candidate_capsules_with_runtime",
    "rows": 3,
    "output_sha256": sys.argv[4],
    "generator_sha256": sys.argv[6],
    "expected_source_verifier_sha256": "a5907b0af2b00d7b530edf0148a3c0aaa1016fe4d96554be2582ea31ce2f3148",
    "expected_runtime_driver_sha256": sys.argv[7],
    "expected_ldd_sha256": "2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5",
}
failures = [
    "replay:" + key
    for key, value in expected_replay.items()
    if replay.get(key) != value
] + [
    "capsules:" + key
    for key, value in expected_capsules.items()
    if capsules.get(key) != value
]
for label, checks in (replay.get("candidate_checks") or {}).items():
    if not label or not checks or not all(checks.values()):
        failures.append("replay:candidate_checks")
for label, checks in (capsules.get("checks") or {}).items():
    if not label or not checks or not all(checks.values()):
        failures.append("capsules:checks")
if len(replay.get("candidate_checks") or {}) != 3:
    failures.append("replay:candidate_count")
if len(capsules.get("checks") or {}) != 3:
    failures.append("capsules:candidate_count")
if failures:
    raise SystemExit(f"registry receipt mismatch: {failures}")
PY

mapfile -d '' -t metadata < <(
    /usr/bin/python3 -I - "$registry" "$capsules" \
        "$SLURM_ARRAY_TASK_ID" <<'PY'
import csv
from pathlib import Path
import sys

def rows(path):
    with Path(path).open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))

routes = rows(sys.argv[1])
capsules = rows(sys.argv[2])
index = int(sys.argv[3])
if len(routes) != 5 or len(capsules) != 3 or index not in range(5):
    raise SystemExit("registry has an unexpected shape")
by_label = {row["candidate"]: row for row in capsules}
if len(by_label) != 3:
    raise SystemExit("capsule registry repeats labels")
route = routes[index]
candidate = by_label.get(route["rebuild_candidate"])
if candidate is None or route["rebuild_source_commit"] != candidate["commit"]:
    raise SystemExit("route is not bound to its exact-source capsule")
keys = (
    "ontology", "candidate", "commit", "binary", "peer_binary",
    "binary_sha256", "source_manifest_sha256", "build_receipt",
    "build_receipt_sha256", "test_receipt", "test_receipt_sha256",
    "source_identity", "source_identity_sha256", "runtime_summary",
    "runtime_summary_sha256", "runtime_manifest_sha256",
    "runtime_library_count",
)
combined = {**candidate, "ontology": route["ontology"]}
for key in keys:
    value = combined.get(key, "")
    if not value or "\0" in value or "\n" in value:
        raise SystemExit(f"invalid registry field: {key}")
    sys.stdout.write(value + "\0")
PY
)
[[ ${#metadata[@]} -eq 17 ]]
ontology=${metadata[0]}
candidate=${metadata[1]}
source_commit=${metadata[2]}
current_binary=${metadata[3]}
current_binary_peer=${metadata[4]}
current_binary_sha256=${metadata[5]}
source_manifest_sha256=${metadata[6]}
build_receipt=${metadata[7]}
build_receipt_sha256=${metadata[8]}
test_receipt=${metadata[9]}
test_receipt_sha256=${metadata[10]}
source_identity=${metadata[11]}
source_identity_sha256=${metadata[12]}
runtime_capture=${metadata[13]}
runtime_capture_summary_sha256=${metadata[14]}
km_runtime_stream_sha256=${metadata[15]}
km_runtime_count=${metadata[16]}
runtime_dir=$(/usr/bin/dirname "$runtime_capture")
capsule_dir=$(/usr/bin/dirname "$current_binary")
test_dir=$(/usr/bin/dirname "$test_receipt")
source_manifest=$capsule_dir/source-files.sha256
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]
[[ $source_commit =~ ^[0-9a-f]{40}$ ]]
for path in "$current_binary" "$current_binary_peer" "$build_receipt" \
    "$source_manifest" "$test_receipt" "$source_identity" \
    "$runtime_capture" "$runtime_dir/runtime-files.sha256"; do
    [[ -s $path && ! -L $path ]]
done
for directory in "$capsule_dir" "$test_dir" "$runtime_dir" \
    "$(/usr/bin/dirname "$source_identity")"; do
    [[ -d $directory && ! -L $directory ]]
    [[ $(/usr/bin/find "$directory" -maxdepth 1 -type l | /usr/bin/wc -l) -eq 0 ]]
    [[ $(/usr/bin/find "$directory" -maxdepth 1 -perm /222 | /usr/bin/wc -l) -eq 0 ]]
done
[[ $(/usr/bin/sha256sum "$current_binary" | /usr/bin/awk '{print $1}') == "$current_binary_sha256" ]]
[[ $(/usr/bin/sha256sum "$current_binary_peer" | /usr/bin/awk '{print $1}') == "$current_binary_sha256" ]]
/usr/bin/cmp -s "$current_binary" "$current_binary_peer"
[[ $(/usr/bin/sha256sum "$source_manifest" | /usr/bin/awk '{print $1}') == "$source_manifest_sha256" ]]
[[ $(/usr/bin/sha256sum "$build_receipt" | /usr/bin/awk '{print $1}') == "$build_receipt_sha256" ]]
[[ $(/usr/bin/sha256sum "$test_receipt" | /usr/bin/awk '{print $1}') == "$test_receipt_sha256" ]]
[[ $(/usr/bin/sha256sum "$source_identity" | /usr/bin/awk '{print $1}') == "$source_identity_sha256" ]]
[[ $(/usr/bin/sha256sum "$runtime_capture" | /usr/bin/awk '{print $1}') == "$runtime_capture_summary_sha256" ]]
[[ $(/usr/bin/sha256sum "$runtime_dir/runtime-files.sha256" | /usr/bin/awk '{print $1}') == "$km_runtime_stream_sha256" ]]
[[ $(/usr/bin/wc -l < "$runtime_dir/runtime-files.sha256") -eq $km_runtime_count ]]

# Verify all candidate receipts once more immediately before execution.
/usr/bin/python3 -I - "$build_receipt" "$test_receipt" "$source_identity" \
    "$runtime_capture" "$source_commit" "$current_binary_sha256" \
    "$source_manifest_sha256" "$build_receipt_sha256" \
    "$test_receipt_sha256" "$source_identity_sha256" \
    "$km_runtime_stream_sha256" "$km_runtime_count" \
    "$runtime_driver_sha256" <<'PY'
import csv
import json
from pathlib import Path
import sys

build = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
tests = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
identity = json.loads(Path(sys.argv[3]).read_text(encoding="utf-8"))
with Path(sys.argv[4]).open(newline="", encoding="utf-8") as handle:
    runtime = {row["field"]: row["value"] for row in csv.DictReader(handle, delimiter="\t")}
commit, binary, source, build_sha, test_sha, identity_sha, runtime_sha, count, driver = sys.argv[5:]
checks = {
    "build": build.get("status") == "verified_reproducible"
        and (build.get("outputs") or {}).get("byte_identical") is True
        and (build.get("outputs") or {}).get("build_a_sha256") == binary
        and (build.get("outputs") or {}).get("build_b_sha256") == binary
        and (build.get("source") or {}).get("manifest_sha256") == source,
    "tests": tests.get("status") == "verified_full_tests"
        and tests.get("failed") == 0
        and tests.get("return_code") == 0
        and tests.get("capsule_build_receipt_sha256") == build_sha,
    "identity": identity.get("status") == "verified_exact_git_source"
        and identity.get("commit") == commit
        and identity.get("source_manifest_sha256") == source
        and identity.get("build_receipt_sha256") == build_sha,
    "runtime": runtime.get("status") == "captured_for_later_independent_recheck"
        and runtime.get("source_commit") == commit
        and runtime.get("binary_sha256") == binary
        and runtime.get("source_manifest_sha256") == source
        and runtime.get("build_receipt_sha256") == build_sha
        and runtime.get("test_receipt_sha256") == test_sha
        and runtime.get("source_identity_sha256") == identity_sha
        and runtime.get("runtime_library_manifest_sha256") == runtime_sha
        and runtime.get("runtime_library_count") == count
        and runtime.get("driver_sha256") == driver,
}
if not all(checks.values()):
    raise SystemExit([key for key, value in checks.items() if not value])
PY

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

hermit_build_root=$routing_root/hermit-oracle-build-49214869
hermit_java=$km_root/bench/jdk8u492-b09/bin/java
hermit_oracle=$hermit_build_root/build-a/Oracle.class
hermit_source=$hermit_build_root/Oracle.java
hermit_classpath=$hermit_build_root/build-a:$km_root/bench/hermit_cp/'*'

for pair in \
    "$konclude:$konclude_sha256" \
    "$konclude_peer:$konclude_sha256" \
    "$konclude_build_receipt:$konclude_build_receipt_sha256" \
    "$konclude_root/source-files.sha256:$konclude_source_manifest_sha256" \
    "$konclude_build_driver:$konclude_build_driver_sha256" \
    "$konclude_root/runtime-files.sha256:$konclude_runtime_stream_sha256" \
    "/usr/bin/ldd:$ldd_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -s $path && ! -L $path ]]
    [[ $(/usr/bin/sha256sum "$path" | /usr/bin/awk '{print $1}') == "$expected" ]]
done
/usr/bin/cmp -s "$konclude" "$konclude_peer"

result_root=$routing_root/source-bound-exact-candidates-${SLURM_ARRAY_JOB_ID}
result_path=$result_root/results/$ontology.json
[[ ! -e $result_path ]]
/usr/bin/mkdir -p "$result_root/results" "$result_root/failures" \
    "$result_root/fingerprints"

validator_environment=(
    PATH=/usr/bin:/bin
    LC_ALL=C
    PYTHONHASHSEED=0
    SLURM_JOB_ID="$SLURM_JOB_ID"
    SLURM_ARRAY_JOB_ID="$SLURM_ARRAY_JOB_ID"
    SLURM_ARRAY_TASK_ID="$SLURM_ARRAY_TASK_ID"
    SLURM_CPUS_PER_TASK="$SLURM_CPUS_PER_TASK"
)
if [[ -n ${SLURM_TMPDIR:-} ]]; then
    validator_environment+=(SLURM_TMPDIR="$SLURM_TMPDIR" TMPDIR="$SLURM_TMPDIR")
fi

/usr/bin/env -i "${validator_environment[@]}" \
    /usr/bin/python3 -I "$validator" \
        --registry "$registry" \
        --row-index "$SLURM_ARRAY_TASK_ID" \
        --expected-registry-row-count 5 \
        --validation-protocol reproducible-exact-candidate-selected-full-iri-v1 \
        --route-observation-policy runtime-trace \
        --km-root "$km_root" \
        --runner "$runner" \
        --fingerprint "$fingerprint" \
        --validation-driver "$validation_driver" \
        --validation-driver-sha256 "$driver_sha256" \
        --konclude "$konclude" \
        --konclude-sha256 "$konclude_sha256" \
        --konclude-library-dir "$konclude_library_dir" \
        --konclude-runtime-count "$konclude_runtime_count" \
        --konclude-runtime-stream-sha256 "$konclude_runtime_stream_sha256" \
        --konclude-build-receipt "$konclude_build_receipt" \
        --konclude-build-receipt-sha256 "$konclude_build_receipt_sha256" \
        --konclude-source-manifest-sha256 "$konclude_source_manifest_sha256" \
        --konclude-build-driver "$konclude_build_driver" \
        --konclude-build-driver-sha256 "$konclude_build_driver_sha256" \
        --ldd-sha256 "$ldd_sha256" \
        --hermit-java "$hermit_java" \
        --hermit-java-sha256 854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619 \
        --hermit-javac-sha256 72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3 \
        --hermit-oracle "$hermit_oracle" \
        --hermit-oracle-sha256 60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619 \
        --hermit-source "$hermit_source" \
        --hermit-source-sha256 b4aec58a97cdea3a0c851b91b5342310f03484e73dbe320d037f71e4f4cd763b \
        --hermit-classpath "$hermit_classpath" \
        --hermit-classpath-manifest "$hermit_build_root/hermit-classpath.sha256" \
        --hermit-classpath-manifest-sha256 56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919 \
        --hermit-classpath-count 81 \
        --hermit-jdk-manifest "$hermit_build_root/jdk-files.sha256" \
        --hermit-jdk-manifest-sha256 bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0 \
        --hermit-jdk-count 405 \
        --hermit-jdk-symlinks "$hermit_build_root/jdk-symlinks.tsv" \
        --hermit-jdk-symlinks-sha256 6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff \
        --hermit-jdk-symlink-count 2 \
        --hermit-runtime-count 5 \
        --hermit-runtime-stream-sha256 d36b6c586e5cfc0b2929266c1715d86c51d0e91c75e63b4e9df5bc1fd405c975 \
        --hermit-build-receipt "$hermit_build_root/build-receipt.json" \
        --hermit-build-receipt-sha256 46f1ac80ca8730b39e0d30604602d72400271d229dd3daa382cf6a89a70445d0 \
        --hermit-build-driver "$routing_root/validation-drivers/sha256-b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52/ibex_rebuild_hermit_oracle.sbatch" \
        --hermit-build-driver-sha256 b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52 \
        --core-root "$routing_root/tail-validation-20260718/cores" \
        --result-dir "$result_root" \
        --binary-override "$current_binary" \
        --binary-override-sha256 "$current_binary_sha256" \
        --source-manifest-sha256 "$source_manifest_sha256" \
        --build-receipt "$build_receipt" \
        --build-receipt-sha256 "$build_receipt_sha256" \
        --km-runtime-count "$km_runtime_count" \
        --km-runtime-stream-sha256 "$km_runtime_stream_sha256" \
        --timeout 240 \
        --reference-timeout 240 \
        --memcap-mb 20480 \
        --reference-memcap-mb 20480
