#!/bin/bash
# Replay every documented alternative route with capsule-10. Each result is
# compared with the exact source-built reference from the selected-route run.
# Submit twice: TASK_OFFSET=0 with array 0-9999, then TASK_OFFSET=10000 with
# array 0-754. Historical executables are provenance only and are never run.
#SBATCH --job-name=km-source-alt
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-9999%48
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%A_%a.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "alternative replay failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_source_alternative_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    requested_offset=${TASK_OFFSET:?submit with TASK_OFFSET=0 or TASK_OFFSET=10000}
    requested_campaign_tag=${CAMPAIGN_TAG:-20260721-01-capsule10}
    [[ $requested_campaign_tag =~ ^[a-z0-9-]+$ ]]
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        TASK_OFFSET="$requested_offset" \
        CAMPAIGN_TAG="$requested_campaign_tag" \
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
        TASK_OFFSET|CAMPAIGN_TAG|SLURM_JOB_ID|SLURM_ARRAY_JOB_ID|SLURM_ARRAY_TASK_ID|\
        SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 16 ]]
case "$TASK_OFFSET" in
    0) [[ $SLURM_ARRAY_TASK_ID -ge 0 && $SLURM_ARRAY_TASK_ID -le 9999 ]] ;;
    10000) [[ $SLURM_ARRAY_TASK_ID -ge 0 && $SLURM_ARRAY_TASK_ID -le 754 ]] ;;
    *) echo "invalid TASK_OFFSET: $TASK_OFFSET" >&2; exit 2 ;;
esac
row_index=$((TASK_OFFSET + SLURM_ARRAY_TASK_ID))
[[ $row_index -ge 0 && $row_index -le 10754 ]]
[[ $CAMPAIGN_TAG =~ ^[a-z0-9-]+$ ]]

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
validation_driver=$submit_dir/ibex_confirm_source_bound_alternatives.sbatch

manifest=$submit_dir/alternative-route-manifest-source-bound.tsv
manifest_sha256=e863cdd77d10bf17e68afbd53126a55741f95c135ba9aceb53c94caa37a743f2
manifest_receipt=$submit_dir/manifest-receipt.json
manifest_receipt_sha256=a36e51511da854c7f8654cb2a12b6e6b0f1fe23343b2ccb77173594b69dfe5d8
manifest_generator=$submit_dir/build_alternative_manifest.py
manifest_generator_sha256=f19b55f59ef4d7df25bdcf9440612784a42ad9c5394ea07e760ac00be12a343b
frozen_registry=$submit_dir/ontology-routes-base.tsv
frozen_registry_sha256=90eff8539618605b1ccdef5b367518ea8cbc5f6a19d14deabe909abef86e64ea
selected_registry=$submit_dir/ontology-solve-routes-source-bound.tsv
selected_registry_sha256=9515703a4343782ebcae3ba414390a1b063f91c0e119af412bdbad0b56ddd72b
validator=$submit_dir/validate_alternative_route.py
validator_sha256=72952c039ea7807796e7df948b9bc0e96e7eb305b6f5d844ff80a5b7ea5c1390
shared_validator=$submit_dir/validate_documented_route.py
shared_validator_sha256=017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08
runner=$submit_dir/reproducible_route_runner.py
runner_sha256=2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c
inner_runner=$submit_dir/validate_tail_runner.py
inner_runner_sha256=8d7c15ec8391b2ef51798103cd79009ef1b6e4a8a0d0899b2c364805a2f8f1f4
fingerprint=$submit_dir/fingerprint_tail_fulliri.py
fingerprint_sha256=b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6

selected_validation_driver_sha256=672678599c0db07b2d0ed62a1afe1304783a84e8220cc1b96eaa83b47502b53d
selected_summary_sha256=82b300115a0cc7ee4d459065b9f3733aa76473444824b91be4948f5472e7e8da
selected_result_manifest_sha256=a855926e03b43e53f543e431f26cb5581b89314eb25251768e37aa7c7ad629fd
selected_result_dir=$routing_root/source-bound-selected-49245587
selected_summary=$selected_result_dir/selected-summary.json
result_root=$routing_root/source-bound-alternatives-$CAMPAIGN_TAG

capsule=$routing_root/reproducible-current-20260721-10-core
current_binary=$capsule/km-build-a
current_binary_peer=$capsule/km-build-b
current_binary_sha256=e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30
source_manifest_sha256=4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794
build_receipt=$capsule/build-receipt.json
build_receipt_sha256=c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda
km_runtime_count=6
km_runtime_stream_sha256=ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5
runtime_capture=$routing_root/runtime-closures/capsule10-capture-20260721-01
runtime_capture_summary_sha256=878ce82360655db0bc86e9249f279cdc05ee5ba8f0a0e37c77975f80c1aba0c1

konclude_root=$routing_root/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
konclude=$konclude_root/Konclude-build-a
konclude_peer=$konclude_root/Konclude-build-b
konclude_sha256=e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4
konclude_runtime_count=33
konclude_runtime_stream_sha256=b26f41184a6a414e13213dbd0059fd8ba49a229f7017f113f5d6bac34ecab123
konclude_build_receipt=$konclude_root/build-receipt.json
konclude_build_receipt_sha256=e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651
konclude_source_manifest_sha256=a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2
konclude_build_driver=$konclude_root/ibex_build_reproducible_konclude.sbatch
konclude_build_driver_sha256=f10514068f31c14da2187f8ebe14dd400f39b36a310a84f6cac811a20d14c6d5

ldd_sha256=2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5
python_sha256=aa7912dd08c81863f3ab6f7018d785c49906755f57efd7e552600fd93343f1d1

sha_of() {
    /usr/bin/sha256sum "$1" | /usr/bin/awk '{print $1}'
}

expected_submit_entries=(
    alternative-route-manifest-source-bound.tsv
    build_alternative_manifest.py
    fingerprint_tail_fulliri.py
    ibex_confirm_source_bound_alternatives.sbatch
    manifest-receipt.json
    ontology-routes-base.tsv
    ontology-solve-routes-source-bound.tsv
    reproducible_route_runner.py
    validate_alternative_route.py
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
    "$manifest:$manifest_sha256" \
    "$manifest_receipt:$manifest_receipt_sha256" \
    "$manifest_generator:$manifest_generator_sha256" \
    "$frozen_registry:$frozen_registry_sha256" \
    "$selected_registry:$selected_registry_sha256" \
    "$validator:$validator_sha256" \
    "$shared_validator:$shared_validator_sha256" \
    "$runner:$runner_sha256" \
    "$inner_runner:$inner_runner_sha256" \
    "$fingerprint:$fingerprint_sha256" \
    "$selected_summary:$selected_summary_sha256" \
    "$current_binary:$current_binary_sha256" \
    "$current_binary_peer:$current_binary_sha256" \
    "$build_receipt:$build_receipt_sha256" \
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
    "/usr/bin/python3:$python_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    /usr/bin/test -s "$path"
    [[ $(sha_of "$path") == "$expected" ]]
done
/usr/bin/cmp -s "$current_binary" "$current_binary_peer"
/usr/bin/cmp -s "$konclude" "$konclude_peer"
[[ -d $selected_result_dir && ! -L $selected_result_dir ]]
[[ -d $konclude_root/runtime-lib && ! -L $konclude_root/runtime-lib ]]
[[ $(/usr/bin/find "$konclude_root" -type l | /usr/bin/wc -l) -eq 0 ]]
[[ $(/usr/bin/find "$konclude_root" -perm /222 | /usr/bin/wc -l) -eq 0 ]]

/usr/bin/python3 -I - \
    "$manifest_receipt" "$manifest_sha256" "$manifest_generator_sha256" \
    "$frozen_registry_sha256" "$selected_registry_sha256" \
    "$selected_summary_sha256" "$selected_result_manifest_sha256" \
    "$current_binary_sha256" "$source_manifest_sha256" \
    "$build_receipt_sha256" <<'PY'
import json
from pathlib import Path
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
expected = {
    "status": "source_bound_alternative_manifest",
    "claim_rows": 10_755,
    "output_sha256": sys.argv[2],
    "generator_sha256": sys.argv[3],
    "frozen_registry_sha256": sys.argv[4],
    "selected_registry_sha256": sys.argv[5],
    "selected_summary_sha256": sys.argv[6],
    "selected_result_manifest_sha256": sys.argv[7],
    "current_binary_sha256": sys.argv[8],
    "current_source_manifest_sha256": sys.argv[9],
    "current_build_receipt_sha256": sys.argv[10],
}
mismatches = [key for key, value in expected.items() if receipt.get(key) != value]
if mismatches:
    raise SystemExit(f"alternative manifest receipt mismatch: {mismatches}")
for key in ("current_binary_locator", "current_build_receipt_locator"):
    if not receipt.get(key, "").startswith("ibex:/"):
        raise SystemExit(f"alternative manifest receipt has invalid {key}")
PY

/usr/bin/python3 -I - \
    "$selected_summary" "$selected_registry_sha256" \
    "$selected_result_manifest_sha256" <<'PY'
import json
from pathlib import Path
import sys

summary = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
if summary.get("registry_sha256") != sys.argv[2]:
    raise SystemExit("selected-route summary has another registry")
if summary.get("result_record_manifest_sha256") != sys.argv[3]:
    raise SystemExit("selected-route result stream differs")
if summary.get("registry_rows") != 592 or summary.get("result_records") != 592:
    raise SystemExit("selected-route campaign is incomplete")
if summary.get("missing_records"):
    raise SystemExit("selected-route evidence stream is incomplete")
PY

bucket=$(/usr/bin/printf '%02d' "$((row_index / 1000))")
row_prefix=$(/usr/bin/printf '%05d' "$row_index")
if /usr/bin/find "$result_root/alternative-results/$bucket" -maxdepth 1 \
        -type f -name "${row_prefix}__*.json" \
        -print -quit 2>/dev/null | /usr/bin/grep -q .; then
    echo "alternative result already exists for row $row_index" >&2
    exit 2
fi
/usr/bin/mkdir -p "$result_root/alternative-results/$bucket" \
    "$result_root/alternative-failures/$bucket" "$result_root/fingerprints"

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
        --manifest "$manifest" \
        --manifest-sha256 "$manifest_sha256" \
        --row-index "$row_index" \
        --task-offset "$TASK_OFFSET" \
        --km-root "$km_root" \
        --runner "$runner" \
        --fingerprint "$fingerprint" \
        --validation-driver "$validation_driver" \
        --validation-driver-sha256 "$driver_sha256" \
        --selected-validation-driver-sha256 "$selected_validation_driver_sha256" \
        --selected-registry-sha256 "$selected_registry_sha256" \
        --selected-summary-sha256 "$selected_summary_sha256" \
        --selected-result-manifest-sha256 "$selected_result_manifest_sha256" \
        --selected-result-dir "$selected_result_dir" \
        --result-dir "$result_root" \
        --ldd-sha256 "$ldd_sha256" \
        --km-runtime-count "$km_runtime_count" \
        --km-runtime-stream-sha256 "$km_runtime_stream_sha256" \
        --konclude-sha256 "$konclude_sha256" \
        --konclude-runtime-count "$konclude_runtime_count" \
        --konclude-runtime-stream-sha256 "$konclude_runtime_stream_sha256" \
        --konclude-build-receipt-sha256 "$konclude_build_receipt_sha256" \
        --konclude-source-manifest-sha256 "$konclude_source_manifest_sha256" \
        --konclude-build-driver-sha256 "$konclude_build_driver_sha256" \
        --timeout 240 \
        --memcap-mb 20480
