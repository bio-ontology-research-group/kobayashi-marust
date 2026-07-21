#!/bin/bash
# Replay all nine retained 0d20dd1 routes with a twice-built executable from
# the exact Git source. The historical executable is never run.
#SBATCH --job-name=km-rebuilt-hist
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:38:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=48G
#SBATCH --array=0-8%9
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "rebuilt historical replay failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_rebuilt_historical_env_i_v1__
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
        SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|SLURM_ARRAY_TASK_ID|SLURM_CPUS_PER_TASK|\
        SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 16 ]]
[[ $SLURM_ARRAY_TASK_ID -ge 0 && $SLURM_ARRAY_TASK_ID -le 8 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

km_root=/ibex/scratch/hohndor/km
routing_root=$km_root/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
validation_driver=$submit_dir/ibex_confirm_rebuilt_historical_routes.sbatch

registry=$submit_dir/rebuilt-historical-routes-source-bound.tsv
registry_sha256=6c6bc5334afcc8274f243c64798d6b6ba964a7ca5e3fd3bceb3e1757c098fb20
registry_receipt=$submit_dir/registry-receipt.json
registry_receipt_sha256=84f66e9e17099907c4dde266d9281e0c05d434ce881ad106930d9eadd79e74bd
registry_generator=$submit_dir/build_rebuilt_historical_registry.py
registry_generator_sha256=eb326863e6ebaf8d45f9b29c92a92cf88bf3ec280812130eb326bd5782237182
source_identity=$submit_dir/rebuilt-0d20dd1-source-identity.json
source_identity_sha256=fa1810baebf9d4af5e2f78d215450ec1211c160f8c85ea00def8000a41b6964e
source_verifier=$submit_dir/verify_rebuilt_source_commit.py
source_verifier_sha256=97770f1a314d56beedcb33d9d7437a4d3f036cd7df2242aac2128217bb38d1ab
validator=$submit_dir/validate_documented_route.py
validator_sha256=f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc
runner=$submit_dir/reproducible_route_runner.py
runner_sha256=2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6

capsule_root=$routing_root/reproducible-0d20dd1-20260721-01
capsule=$capsule_root/capsule
tests=$capsule_root/tests
current_binary=$capsule/km-build-a
current_binary_peer=$capsule/km-build-b
current_binary_sha256=ced4544f50a988f7a07059195ce38a6fca65f0692998c31dce656f513ad66a57
source_manifest_sha256=f6b393cbda6448ccd255f1b109385134eed8b441439826b70b2e1ccd0a169537
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=9a6eb331df6b86710862eef62878df082f9160f04104a242580d132ef2434ed1
test_receipt=$tests/test-receipt.json
test_receipt_sha256=bac2429376aad6ff2409f55b9af6a52ef162e2e6dc5fb0c48c7c6df52111d006
runtime_capture=$routing_root/runtime-closures/0d20dd1-capture-20260721-01
runtime_capture_summary_sha256=34f2b86ef60c745a40039c65025b633f97b1b3bf9442c1cf23c08c1a79d5dbd0
km_runtime_count=5
km_runtime_stream_sha256=8c7fd69fcc25283170d11e2b5d9cd6c6187c9bce56f0fd4ee7654e567cb94d00

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
gnu_time_sha256=db73dfb29414b2a3c9ba7bb85bf10c1e32644c51f2918813398f75eaccbb45a6

# The two adjudicated rows use the source-built HermiT oracle; the remaining
# seven use source-built Konclude. Keep both complete identities explicit.
hermit_build_root=$routing_root/hermit-oracle-build-49214869
hermit_java=$km_root/bench/jdk8u492-b09/bin/java
hermit_oracle=$hermit_build_root/build-a/Oracle.class
hermit_source=$hermit_build_root/Oracle.java
hermit_classpath=$hermit_build_root/build-a:$km_root/bench/hermit_cp/'*'

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

expected_submit_entries=(
    build_rebuilt_historical_registry.py
    fingerprint_tail_fulliri.py
    ibex_confirm_rebuilt_historical_routes.sbatch
    rebuilt-0d20dd1-source-identity.json
    rebuilt-historical-routes-source-bound.tsv
    registry-receipt.json
    reproducible_route_runner.py
    validate_documented_route.py
    validate_tail_runner.py
    verify_rebuilt_source_commit.py
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
    "$registry:$registry_sha256" \
    "$registry_receipt:$registry_receipt_sha256" \
    "$registry_generator:$registry_generator_sha256" \
    "$source_identity:$source_identity_sha256" \
    "$source_verifier:$source_verifier_sha256" \
    "$validator:$validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$current_binary:$current_binary_sha256" \
    "$current_binary_peer:$current_binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
    "$test_receipt:$test_receipt_sha256" \
    "$capsule/source-files.sha256:$source_manifest_sha256" \
    "$runtime_capture/SUMMARY.tsv:$runtime_capture_summary_sha256" \
    "$runtime_capture/runtime-files.sha256:$km_runtime_stream_sha256" \
    "$konclude:$konclude_sha256" \
    "$konclude_peer:$konclude_sha256" \
    "$konclude_build_receipt:$konclude_build_receipt_sha256" \
    "$konclude_root/source-files.sha256:$konclude_source_manifest_sha256" \
    "$konclude_build_driver:$konclude_build_driver_sha256" \
    "$konclude_root/runtime-files.sha256:$konclude_runtime_stream_sha256" \
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
[[ $(/usr/bin/find "$capsule_root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$capsule_root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$konclude_root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$konclude_root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]

/usr/bin/python3 -I - "$registry_receipt" "$registry_sha256" \
    "$registry_generator_sha256" "$source_identity_sha256" \
    "$current_binary_sha256" "$source_manifest_sha256" \
    "$build_receipt_sha256" "$test_receipt_sha256" \
    "$runtime_capture_summary_sha256" "$km_runtime_stream_sha256" <<'PY'
import json
from pathlib import Path
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
expected = {
    "status": "source_bound_rebuilt_historical_registry",
    "rows": 9,
    "output_sha256": sys.argv[2],
    "generator_sha256": sys.argv[3],
    "source_identity_sha256": sys.argv[4],
    "binary_sha256": sys.argv[5],
    "source_manifest_sha256": sys.argv[6],
    "build_receipt_sha256": sys.argv[7],
    "test_receipt_sha256": sys.argv[8],
    "runtime_summary_sha256": sys.argv[9],
    "runtime_manifest_sha256": sys.argv[10],
}
mismatches = [key for key, value in expected.items() if receipt.get(key) != value]
if mismatches or not all((receipt.get("checks") or {}).values()):
    raise SystemExit(f"rebuilt route registry receipt mismatch: {mismatches}")
PY

ontology=$(/usr/bin/awk -F '\t' -v line="$((SLURM_ARRAY_TASK_ID + 2))" \
    'NR == line {print $1}' "$registry")
[[ $ontology =~ ^ore_ont_[0-9]+\.owl$ ]]

result_root=$routing_root/source-bound-rebuilt-historical-${SLURM_ARRAY_JOB_ID}
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
        --expected-registry-row-count 9 \
        --validation-protocol reproducible-rebuilt-historical-full-iri-v1 \
        --route-observation-policy closed-manual-environment \
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
