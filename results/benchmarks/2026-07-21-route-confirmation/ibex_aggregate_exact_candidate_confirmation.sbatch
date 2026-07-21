#!/bin/bash
# Strictly aggregate the five exact-source candidate route replays.
#SBATCH --job-name=km-exact-agg
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "exact candidate aggregation failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_exact_candidate_aggregate_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        REPLAY_REGISTRY="${REPLAY_REGISTRY:?export the five-row replay registry}" \
        REPLAY_REGISTRY_SHA256="${REPLAY_REGISTRY_SHA256:?export its SHA-256}" \
        REPLAY_REGISTRY_RECEIPT="${REPLAY_REGISTRY_RECEIPT:?export its receipt}" \
        REPLAY_REGISTRY_RECEIPT_SHA256="${REPLAY_REGISTRY_RECEIPT_SHA256:?export the receipt SHA-256}" \
        CAPSULE_REGISTRY="${CAPSULE_REGISTRY:?export the final capsule registry}" \
        CAPSULE_REGISTRY_SHA256="${CAPSULE_REGISTRY_SHA256:?export its SHA-256}" \
        CAPSULE_REGISTRY_RECEIPT="${CAPSULE_REGISTRY_RECEIPT:?export its receipt}" \
        CAPSULE_REGISTRY_RECEIPT_SHA256="${CAPSULE_REGISTRY_RECEIPT_SHA256:?export the receipt SHA-256}" \
        REPLAY_RESULT_DIR="${REPLAY_RESULT_DIR:?export the completed replay result directory}" \
        REPLAY_ARRAY_JOB_ID="${REPLAY_ARRAY_JOB_ID:?export the replay array job ID}" \
        REPLAY_DRIVER_SHA256="${REPLAY_DRIVER_SHA256:?export the replay driver SHA-256}" \
        AGGREGATE_ROOT="${AGGREGATE_ROOT:?export a new aggregate root}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        REPLAY_REGISTRY|REPLAY_REGISTRY_SHA256|REPLAY_REGISTRY_RECEIPT|\
        REPLAY_REGISTRY_RECEIPT_SHA256|CAPSULE_REGISTRY|\
        CAPSULE_REGISTRY_SHA256|CAPSULE_REGISTRY_RECEIPT|\
        CAPSULE_REGISTRY_RECEIPT_SHA256|REPLAY_RESULT_DIR|\
        REPLAY_ARRAY_JOB_ID|REPLAY_DRIVER_SHA256|AGGREGATE_ROOT|\
        SLURM_JOB_ID|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_aggregate_exact_candidate_confirmation.sbatch
aggregator=$submit_dir/aggregate_exact_candidate_confirmation.py
aggregator_sha256=bcc0775b95a213485c5bf05ec1e53e68a647b04a1d07dca462ac08481f992405
for pair in "$submit_copy:$driver_sha256" "$aggregator:$aggregator_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -s $path && ! -L $path ]]
    [[ $(/usr/bin/sha256sum "$path" | /usr/bin/awk '{print $1}') == "$expected" ]]
done
[[ $(/usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -type f | /usr/bin/wc -l) -eq 2 ]]

for specification in \
    "$REPLAY_REGISTRY:$REPLAY_REGISTRY_SHA256" \
    "$REPLAY_REGISTRY_RECEIPT:$REPLAY_REGISTRY_RECEIPT_SHA256" \
    "$CAPSULE_REGISTRY:$CAPSULE_REGISTRY_SHA256" \
    "$CAPSULE_REGISTRY_RECEIPT:$CAPSULE_REGISTRY_RECEIPT_SHA256"; do
    path=${specification%%:*}
    expected=${specification##*:}
    [[ -s $path && ! -L $path ]]
    [[ $(/usr/bin/sha256sum "$path" | /usr/bin/awk '{print $1}') == "$expected" ]]
done
[[ $REPLAY_ARRAY_JOB_ID =~ ^[0-9]+$ ]]
[[ $REPLAY_RESULT_DIR == /ibex/scratch/hohndor/km/routing_20260715/source-bound-exact-candidates-$REPLAY_ARRAY_JOB_ID ]]
[[ -d $REPLAY_RESULT_DIR && ! -L $REPLAY_RESULT_DIR ]]
[[ $AGGREGATE_ROOT == /ibex/scratch/hohndor/km/routing_20260715/source-bound-exact-candidate-aggregation-* ]]
[[ ! -e $AGGREGATE_ROOT ]]
/usr/bin/mkdir "$AGGREGATE_ROOT"

/usr/bin/python3 -I "$aggregator" \
    --registry "$REPLAY_REGISTRY" \
    --registry-sha256 "$REPLAY_REGISTRY_SHA256" \
    --registry-receipt "$REPLAY_REGISTRY_RECEIPT" \
    --registry-receipt-sha256 "$REPLAY_REGISTRY_RECEIPT_SHA256" \
    --registry-generator-sha256 15b7a4ba62c730ffde57f79783c66bce6da7f5b43dd77998742e58970942230c \
    --candidate-capsules "$CAPSULE_REGISTRY" \
    --candidate-capsules-sha256 "$CAPSULE_REGISTRY_SHA256" \
    --candidate-capsules-receipt "$CAPSULE_REGISTRY_RECEIPT" \
    --candidate-capsules-receipt-sha256 "$CAPSULE_REGISTRY_RECEIPT_SHA256" \
    --candidate-capsules-generator-sha256 729212823439e0fb39f66ebd9ed0522672c9df52a6a8eadd5c0bd64169d8d07b \
    --expected-source-verifier-sha256 a5907b0af2b00d7b530edf0148a3c0aaa1016fe4d96554be2582ea31ce2f3148 \
    --expected-runtime-driver-sha256 c619a815cc9667fd8c63236c3f33ac7a8c78290a65f4036e2acb235ed3fe0f90 \
    --result-dir "$REPLAY_RESULT_DIR" \
    --summary-json "$AGGREGATE_ROOT/exact-candidate-summary.json" \
    --summary-tsv "$AGGREGATE_ROOT/exact-candidate-summary.tsv" \
    --expected-selected-registry-sha256 9515703a4343782ebcae3ba414390a1b063f91c0e119af412bdbad0b56ddd72b \
    --expected-slurm-array-job-id "$REPLAY_ARRAY_JOB_ID" \
    --expected-timeout 240 \
    --expected-memcap-mb 20480 \
    --expected-ldd-sha256 2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5 \
    --expected-validator-sha256 f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc \
    --expected-validation-driver-sha256 "$REPLAY_DRIVER_SHA256" \
    --expected-runner-sha256 2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c \
    --expected-fingerprint-tool-sha256 b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6 \
    --expected-konclude-sha256 e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4 \
    --expected-konclude-runtime-sha256 b26f41184a6a414e13213dbd0059fd8ba49a229f7017f113f5d6bac34ecab123 \
    --expected-konclude-build-receipt-sha256 e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651 \
    --expected-konclude-source-manifest-sha256 a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2 \
    --expected-konclude-build-driver-sha256 f10514068f31c14da2187f8ebe14dd400f39b36a310a84f6cac811a20d14c6d5 \
    --strict \
    > "$AGGREGATE_ROOT/aggregator.stdout.json"

(
    cd "$AGGREGATE_ROOT"
    /usr/bin/find . -maxdepth 1 -type f -printf '%f\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$AGGREGATE_ROOT/artifacts.sha256"
/usr/bin/chmod a-w "$AGGREGATE_ROOT"/*
/usr/bin/chmod a-w "$AGGREGATE_ROOT"
/usr/bin/cat "$AGGREGATE_ROOT/exact-candidate-summary.json"
