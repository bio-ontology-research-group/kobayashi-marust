#!/bin/bash
# Reproduce the capsule-10 ht_bridge claims for ORE 4669 and 10621 against
# a twice-built official Konclude source capsule. Historical binaries are not
# executed. KM always retains the ORE 240-second and 20-GiB limits.
#SBATCH --job-name=km-final-target10
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:38:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "targeted validation failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_final_target10_env_i_v1__
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
if [[ $# -ne 1 || $1 != "$clean_sentinel" ]]; then
    echo "invalid clean-environment sentinel" >&2
    exit 2
fi
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|SLURM_ARRAY_TASK_ID|SLURM_CPUS_PER_TASK|\
        SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ ${SHLVL:-} == 1 ]]
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
validation_driver=$submit_dir/ibex_validate_final_targeted10.sbatch

registry=$submit_dir/targeted-4669-10621-route-final10.tsv
registry_sha256=9ac1addbdd615d30eb6fddd7fc082b7a2cc88315c8e5e0f69c9d2b10e65a2c4c
validator=$submit_dir/validate_documented_route.py
validator_sha256=017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08
runner=$submit_dir/reproducible_route_runner.py
runner_sha256=2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6

capsule=$routing_root/reproducible-current-20260721-10-core
current_binary=$capsule/km-build-a
current_binary_peer=$capsule/km-build-b
current_binary_sha256=e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30
source_manifest_sha256=4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda
capsule_file_count=22
capsule_stream_sha256=59b7aa29a6b0e6fc85c7ecc34fa960395eaa1b258ed5de122433ebfd9167e9de
km_runtime_count=6
km_runtime_stream_sha256=ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5
runtime_capture=$routing_root/runtime-closures/capsule10-capture-20260721-01
runtime_capture_summary_sha256=878ce82360655db0bc86e9249f279cdc05ee5ba8f0a0e37c77975f80c1aba0c1
runtime_capture_stream_sha256=06d2430ccc48f6e71a6217801bcdb23a6ac251b2a122db894f756c57f960e3cf

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
konclude_capsule_file_count=40
konclude_capsule_stream_sha256=7989e81e07792faa4cf9ea04e645b9ac40ae7112a060dcfe677789d8c5f6fa64

ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6

hermit_build_root=$routing_root/hermit-oracle-build-49214869
hermit_java=$km_root/bench/jdk8u492-b09/bin/java
hermit_java_sha256=854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619
hermit_javac_sha256=72e0a500b28f38b485a4b09849a63605893ad1bae5e15790d591f686b40b23e3
hermit_oracle=$hermit_build_root/build-a/Oracle.class
hermit_oracle_sha256=60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619
hermit_source=$hermit_build_root/Oracle.java
hermit_source_sha256=b4aec58a97cdea3a0c851b91b5342310f03484e73dbe320d037f71e4f4cd763b
hermit_classpath=$hermit_build_root/build-a:$km_root/bench/hermit_cp/'*'
hermit_classpath_manifest=$hermit_build_root/hermit-classpath.sha256
hermit_classpath_manifest_sha256=56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919
hermit_jdk_manifest=$hermit_build_root/jdk-files.sha256
hermit_jdk_manifest_sha256=bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0
hermit_jdk_symlinks=$hermit_build_root/jdk-symlinks.tsv
hermit_jdk_symlinks_sha256=6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff
hermit_runtime_stream_sha256=d36b6c586e5cfc0b2929266c1715d86c51d0e91c75e63b4e9df5bc1fd405c975
hermit_build_receipt=$hermit_build_root/build-receipt.json
hermit_build_receipt_sha256=46f1ac80ca8730b39e0d30604602d72400271d229dd3daa382cf6a89a70445d0
hermit_build_driver=$routing_root/validation-drivers/sha256-b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52/ibex_rebuild_hermit_oracle.sbatch
hermit_build_driver_sha256=b1f434da2c463b756718f0e1e801b4ff1b3ecd46bef895fc63366e82feebeb52

case "$SLURM_ARRAY_TASK_ID" in
    0)
        ontology=ore_ont_4669.owl
        ontology_sha256_expected=2b15dc9535ed50c4dc9eae05067df4e6525b69c7bf1913192715b79ad550b3eb
        reference_timeout=1200
        reference_memcap=40960
        ;;
    1)
        ontology=ore_ont_10621.owl
        ontology_sha256_expected=5d6abde6b2f6e9ebc5c7161c524178749fb165d1885babfb01ce13a997308167
        reference_timeout=240
        reference_memcap=20480
        ;;
    *) echo "invalid task index: $SLURM_ARRAY_TASK_ID" >&2; exit 2 ;;
esac
ontology_path=$km_root/corpus/$ontology
run_root=$routing_root/final-targeted10-${SLURM_ARRAY_JOB_ID}-${SLURM_ARRAY_TASK_ID}
tin=$run_root/${ontology%.owl}.ht-bridge.tinput.json

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

expected_submit_entries=(
    fingerprint_tail_fulliri.py
    ibex_validate_final_targeted10.sbatch
    reproducible_route_runner.py
    targeted-4669-10621-route-final10.tsv
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
for entry in "${expected_submit_entries[@]}"; do
    [[ -f $submit_dir/$entry && ! -L $submit_dir/$entry ]]
done

[[ ! -e $run_root ]]
for temporary in \
    "$run_root.capsule-files.sha256.tmp" \
    "$run_root.runtime-capture-files.sha256.tmp" \
    "$run_root.konclude-capsule-files.sha256.tmp"; do
    [[ ! -e $temporary ]]
done
[[ -f $ontology_path && ! -L $ontology_path ]]
[[ $(sha_of "$ontology_path") == "$ontology_sha256_expected" ]]

for pair in \
    "$validation_driver:$driver_sha256" \
    "$registry:$registry_sha256" \
    "$validator:$validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$current_binary:$current_binary_sha256" \
    "$current_binary_peer:$current_binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$runtime_capture/SUMMARY.tsv:$runtime_capture_summary_sha256" \
    "$runtime_capture/capsule-files.sha256:$capsule_stream_sha256" \
    "$runtime_capture/runtime-files.sha256:$km_runtime_stream_sha256" \
    "$konclude:$konclude_sha256" \
    "$konclude_peer:$konclude_sha256" \
    "$konclude_build_receipt:$konclude_build_receipt_sha256" \
    "$konclude_root/source-files.sha256:$konclude_source_manifest_sha256" \
    "$konclude_build_driver:$konclude_build_driver_sha256" \
    "$konclude_root/runtime-files.sha256:$konclude_runtime_stream_sha256" \
    "$hermit_java:$hermit_java_sha256" \
    "$hermit_oracle:$hermit_oracle_sha256" \
    "$hermit_source:$hermit_source_sha256" \
    "$hermit_classpath_manifest:$hermit_classpath_manifest_sha256" \
    "$hermit_jdk_manifest:$hermit_jdk_manifest_sha256" \
    "$hermit_jdk_symlinks:$hermit_jdk_symlinks_sha256" \
    "$hermit_build_receipt:$hermit_build_receipt_sha256" \
    "$hermit_build_driver:$hermit_build_driver_sha256" \
    "/usr/bin/ldd:$ldd_sha256" \
    "/usr/bin/python3:$python_sha256" \
    "/usr/bin/time:$gnu_time_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$current_binary" "$current_binary_peer"
/usr/bin/cmp -s "$konclude" "$konclude_peer"
[[ -d $konclude_library_dir && ! -L $konclude_library_dir ]]

[[ $(/usr/bin/find "$capsule" -mindepth 1 -maxdepth 1 ! -type f | /usr/bin/wc -l) -eq 0 ]]
(
    cd "$capsule"
    /usr/bin/find . -mindepth 1 -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root.capsule-files.sha256.tmp"
[[ $(/usr/bin/wc -l < "$run_root.capsule-files.sha256.tmp") -eq $capsule_file_count ]]
[[ $(sha_of "$run_root.capsule-files.sha256.tmp") == "$capsule_stream_sha256" ]]

[[ $(/usr/bin/find "$runtime_capture" -mindepth 1 -maxdepth 1 ! -type f | /usr/bin/wc -l) -eq 0 ]]
(
    cd "$runtime_capture"
    /usr/bin/find . -mindepth 1 -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root.runtime-capture-files.sha256.tmp"
[[ $(/usr/bin/wc -l < "$run_root.runtime-capture-files.sha256.tmp") -eq 7 ]]
[[ $(sha_of "$run_root.runtime-capture-files.sha256.tmp") == "$runtime_capture_stream_sha256" ]]

[[ $(/usr/bin/find "$konclude_root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$konclude_root" -type d | /usr/bin/wc -l) -eq 2 ]]
[[ $(/usr/bin/find "$konclude_root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]
(
    cd "$konclude_root"
    /usr/bin/find . -type f -printf '%P\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$run_root.konclude-capsule-files.sha256.tmp"
[[ $(/usr/bin/wc -l < "$run_root.konclude-capsule-files.sha256.tmp") -eq $konclude_capsule_file_count ]]
[[ $(sha_of "$run_root.konclude-capsule-files.sha256.tmp") == "$konclude_capsule_stream_sha256" ]]

/usr/bin/mkdir -p "$run_root"
/usr/bin/mv "$run_root.capsule-files.sha256.tmp" "$run_root/capsule-files.sha256"
/usr/bin/mv "$run_root.runtime-capture-files.sha256.tmp" "$run_root/runtime-capture-files.sha256"
/usr/bin/mv "$run_root.konclude-capsule-files.sha256.tmp" "$run_root/konclude-capsule-files.sha256"

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

set +e
/usr/bin/env -i "${validator_environment[@]}" \
    /usr/bin/python3 -I "$validator" \
        --registry "$registry" \
        --row-index "$SLURM_ARRAY_TASK_ID" \
        --expected-registry-row-count 2 \
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
        --hermit-java-sha256 "$hermit_java_sha256" \
        --hermit-javac-sha256 "$hermit_javac_sha256" \
        --hermit-oracle "$hermit_oracle" \
        --hermit-oracle-sha256 "$hermit_oracle_sha256" \
        --hermit-source "$hermit_source" \
        --hermit-source-sha256 "$hermit_source_sha256" \
        --hermit-classpath "$hermit_classpath" \
        --hermit-classpath-manifest "$hermit_classpath_manifest" \
        --hermit-classpath-manifest-sha256 "$hermit_classpath_manifest_sha256" \
        --hermit-classpath-count 81 \
        --hermit-jdk-manifest "$hermit_jdk_manifest" \
        --hermit-jdk-manifest-sha256 "$hermit_jdk_manifest_sha256" \
        --hermit-jdk-count 405 \
        --hermit-jdk-symlinks "$hermit_jdk_symlinks" \
        --hermit-jdk-symlinks-sha256 "$hermit_jdk_symlinks_sha256" \
        --hermit-jdk-symlink-count 2 \
        --hermit-runtime-count 5 \
        --hermit-runtime-stream-sha256 "$hermit_runtime_stream_sha256" \
        --hermit-build-receipt "$hermit_build_receipt" \
        --hermit-build-receipt-sha256 "$hermit_build_receipt_sha256" \
        --hermit-build-driver "$hermit_build_driver" \
        --hermit-build-driver-sha256 "$hermit_build_driver_sha256" \
        --core-root "$routing_root/tail-validation-20260718/cores" \
        --result-dir "$run_root" \
        --binary-override "$current_binary" \
        --binary-override-sha256 "$current_binary_sha256" \
        --source-manifest-sha256 "$source_manifest_sha256" \
        --build-receipt "$build_receipt" \
        --build-receipt-sha256 "$build_receipt_sha256" \
        --km-runtime-count "$km_runtime_count" \
        --km-runtime-stream-sha256 "$km_runtime_stream_sha256" \
        --dump-tinput "$tin" \
        --timeout 240 \
        --reference-timeout "$reference_timeout" \
        --memcap-mb 20480 \
        --reference-memcap-mb "$reference_memcap"
validator_rc=$?
set -e

set +e
/usr/bin/python3 -I - \
    "$run_root/results/$ontology.json" "$run_root/ACCEPTANCE.json" \
    "$validator_rc" "$ontology" "$ontology_sha256_expected" "$tin" \
    "$current_binary" "$current_binary_sha256" "$source_manifest_sha256" \
    "$build_receipt_sha256" "$km_runtime_stream_sha256" \
    "$konclude" "$konclude_sha256" "$konclude_library_dir" \
    "$konclude_build_receipt_sha256" "$konclude_source_manifest_sha256" \
    "$konclude_build_driver_sha256" "$konclude_runtime_stream_sha256" \
    "$konclude_runtime_count" "$reference_timeout" "$reference_memcap" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

(
    result_text, output_text, validator_rc_text, ontology,
    ontology_sha256, tin_text, km_binary, km_sha256, km_source_sha256,
    km_receipt_sha256, km_runtime_sha256, konclude_binary,
    konclude_sha256, konclude_library_dir, konclude_receipt_sha256,
    konclude_source_sha256, konclude_driver_sha256,
    konclude_runtime_sha256, konclude_runtime_count_text,
    reference_timeout_text, reference_memcap_text,
) = sys.argv[1:]
result_path = Path(result_text)
output_path = Path(output_text)
tin = Path(tin_text)
result = json.loads(result_path.read_text()) if result_path.is_file() else {}
route = result.get("route_specification") or {}
km_run = result.get("km_run") or {}
reference_route = result.get("reference_route_specification") or {}
reference_run = result.get("reference_run") or {}
reference_runtime = result.get("reference_runtime") or {}
expected_reference_environment = {
    "PATH": "/usr/bin:/bin",
    "LC_ALL": "C",
    "PYTHONHASHSEED": "0",
    "LD_LIBRARY_PATH": konclude_library_dir,
}
tin_sha256 = hashlib.sha256(tin.read_bytes()).hexdigest() if tin.is_file() else ""
checks = {
    "validator_exit_zero": int(validator_rc_text) == 0,
    "protocol_v2": result.get("validation_protocol") == "reproducible-current-selected-full-iri-v2",
    "confirmed_exact": result.get("confirmation_status") == "confirmed_exact_full_iri" and result.get("confirmed") is True,
    "ontology": result.get("ontology") == ontology,
    "ontology_sha256": result.get("ontology_sha256") == ontology_sha256,
    "documented_route": result.get("documented_route") == "ht_bridge",
    "requested_route": result.get("effective_route_request") == "ht_bridge",
    "observed_route": result.get("selected_route_trace") == "ht_bridge" and result.get("selected_route_trace_count") == 1,
    "all_validator_checks": bool(result.get("checks")) and all(result["checks"].values()),
    "all_km_runtime_checks": bool(result.get("km_runtime_checks")) and all(result["km_runtime_checks"].values()),
    "all_reference_build_checks": bool(result.get("reference_build_checks")) and all(result["reference_build_checks"].values()),
    "all_reference_runtime_checks": bool(result.get("reference_runtime_checks")) and all(result["reference_runtime_checks"].values()),
    "km_binary": result.get("actual_binary_sha256") == km_sha256 and result.get("executed_binary") == km_binary,
    "km_source": result.get("executed_source_manifest_sha256") == km_source_sha256,
    "km_receipt": result.get("executed_build_receipt_sha256") == km_receipt_sha256,
    "km_runtime": (result.get("km_runtime") or {}).get("runtime_library_manifest_sha256") == km_runtime_sha256,
    "km_limits": route.get("timeout_s") == 240.0 and route.get("memory_limit_mb") == 20480 and km_run.get("status") == "ok",
    "konclude_binary": result.get("reference_binary_sha256") == konclude_sha256 and reference_route.get("binary_sha256") == konclude_sha256 and reference_run.get("binary") == konclude_binary,
    "konclude_receipt": result.get("reference_build_receipt_sha256") == konclude_receipt_sha256 and reference_route.get("build_receipt_sha256") == konclude_receipt_sha256,
    "konclude_source": reference_route.get("source_manifest_sha256") == konclude_source_sha256,
    "konclude_driver": reference_route.get("build_driver_sha256") == konclude_driver_sha256,
    "konclude_runtime": reference_runtime.get("runtime_library_manifest_sha256") == konclude_runtime_sha256 and reference_runtime.get("runtime_library_count") == int(konclude_runtime_count_text),
    "konclude_closed_environment": reference_route.get("environment") == expected_reference_environment and reference_run.get("environment") == {"LD_LIBRARY_PATH": konclude_library_dir},
    "reference_limits": reference_route.get("timeout_s") == float(reference_timeout_text) and reference_route.get("memory_limit_mb") == int(reference_memcap_text),
    "tinput": bool(tin_sha256) and (result.get("tinput_dump") or {}).get("sha256") == tin_sha256,
}
record = {
    "schema_version": 2,
    "status": "accepted" if all(checks.values()) else "rejected",
    "claim": f"{ontology} is reproduced by capsule-10 route ht_bridge against source-built Konclude",
    "checks": checks,
    "validator_return_code": int(validator_rc_text),
    "validation_record": str(result_path),
    "validation_record_sha256": hashlib.sha256(result_path.read_bytes()).hexdigest() if result_path.is_file() else "",
    "tinput_sha256": tin_sha256,
}
temporary = Path(str(output_path) + ".tmp")
temporary.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
temporary.replace(output_path)
print(json.dumps(record, sort_keys=True))
raise SystemExit(0 if record["status"] == "accepted" else 1)
PY
acceptance_rc=$?
set -e

/usr/bin/find "$run_root" -type f -exec /usr/bin/chmod 0444 {} +
/usr/bin/find "$run_root" -type d -exec /usr/bin/chmod 0555 {} +
/usr/bin/sha256sum "$run_root/ACCEPTANCE.json"
if [[ $validator_rc -ne 0 || $acceptance_rc -ne 0 ]]; then
    exit 1
fi
