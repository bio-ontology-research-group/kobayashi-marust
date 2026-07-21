#!/bin/bash
# Aggregate and freeze all nine exact-source historical-route replays.
#SBATCH --job-name=km-rebuilt-agg
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "rebuilt aggregate failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_rebuilt_aggregate_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_CPUS_PER_TASK|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 1 ]]
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

routing_root=/ibex/scratch/hohndor/km/routing_20260715
source_array_job_id=49260043
result_root=$routing_root/source-bound-rebuilt-historical-$source_array_job_id
aggregate_root=$routing_root/source-bound-rebuilt-historical-aggregation-$SLURM_JOB_ID
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
submit_copy=$submit_dir/ibex_aggregate_rebuilt_historical.sbatch
aggregator=$submit_dir/aggregate_route_confirmation.py
aggregator_sha256=dc122d8cf0778248b1c8acb3124877da0ded6239a4e3d87dc0cd14b3c3ac6f5d
registry=$submit_dir/rebuilt-historical-routes-source-bound.tsv
registry_sha256=6c6bc5334afcc8274f243c64798d6b6ba964a7ca5e3fd3bceb3e1757c098fb20
registry_receipt=$submit_dir/registry-receipt.json
registry_receipt_sha256=84f66e9e17099907c4dde266d9281e0c05d434ce881ad106930d9eadd79e74bd

expected_submit_entries=(
    aggregate_route_confirmation.py
    ibex_aggregate_rebuilt_historical.sbatch
    rebuilt-historical-routes-source-bound.tsv
    registry-receipt.json
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
    "$submit_copy:$driver_sha256" \
    "$aggregator:$aggregator_sha256" \
    "$registry:$registry_sha256" \
    "$registry_receipt:$registry_receipt_sha256"; do
    path=${pair%%:*}
    expected=${pair##*:}
    [[ -s $path && ! -L $path ]]
    [[ $(/usr/bin/sha256sum "$path" | /usr/bin/awk '{print $1}') == "$expected" ]]
done
[[ -d $result_root && ! -L $result_root ]]
[[ ! -e $aggregate_root ]]
/usr/bin/mkdir -m 0755 "$aggregate_root"

set +e
/usr/bin/python3 -I "$aggregator" \
    --registry "$registry" \
    --result-dir "$result_root" \
    --summary-json "$aggregate_root/rebuilt-historical-summary.json" \
    --summary-tsv "$aggregate_root/rebuilt-historical-summary.tsv" \
    --expected-registry-sha256 "$registry_sha256" \
    --expected-registry-row-count 9 \
    --expected-validation-protocol reproducible-rebuilt-historical-full-iri-v1 \
    --expected-route-observation-policy closed-manual-environment \
    --expected-slurm-array-job-id "$source_array_job_id" \
    --expected-timeout 240 \
    --expected-memcap-mb 20480 \
    --expected-binary-sha256 ced4544f50a988f7a07059195ce38a6fca65f0692998c31dce656f513ad66a57 \
    --expected-source-manifest-sha256 f6b393cbda6448ccd255f1b109385134eed8b441439826b70b2e1ccd0a169537 \
    --expected-build-receipt-sha256 9a6eb331df6b86710862eef62878df082f9160f04104a242580d132ef2434ed1 \
    --expected-km-runtime-sha256 8c7fd69fcc25283170d11e2b5d9cd6c6187c9bce56f0fd4ee7654e567cb94d00 \
    --expected-ldd-sha256 2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5 \
    --expected-validator-sha256 f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc \
    --expected-validation-driver-sha256 7337b1ea7c179ca468176ae693c66f00a102f7d39ee22220942aa84bf7fe55b2 \
    --expected-runner-sha256 2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c \
    --expected-fingerprint-tool-sha256 b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6 \
    --expected-konclude-sha256 e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4 \
    --expected-konclude-runtime-sha256 b26f41184a6a414e13213dbd0059fd8ba49a229f7017f113f5d6bac34ecab123 \
    --expected-konclude-build-receipt-sha256 e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651 \
    --expected-konclude-source-manifest-sha256 a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2 \
    --expected-konclude-build-driver-sha256 f10514068f31c14da2187f8ebe14dd400f39b36a310a84f6cac811a20d14c6d5 \
    --expected-hermit-oracle-sha256 60258bda6848304b1f113ba1c62c58f017d58fb848c248b45ef2792086a5d619 \
    --expected-hermit-java-sha256 854f27091cbf804f7fa6bfb2d958210740eb55e6d21f59d931f95a354a1a0619 \
    --expected-hermit-build-receipt-sha256 46f1ac80ca8730b39e0d30604602d72400271d229dd3daa382cf6a89a70445d0 \
    --expected-hermit-classpath-sha256 56735fee7357b108c3e19e640f3eeada2d1e37b12cc8b5d76a02e90afb2f9919 \
    --expected-hermit-jdk-sha256 bf22f9455ef1626151371f11269473febaa6a52846bf86c5d486c2f8bba71ea0 \
    --expected-hermit-jdk-symlinks-sha256 6e230e8f5465e17fe01eb8882411810c209456e15cd8c0c8ef495ffad81f42ff \
    --expected-hermit-runtime-sha256 d36b6c586e5cfc0b2929266c1715d86c51d0e91c75e63b4e9df5bc1fd405c975 \
    --strict
aggregate_rc=$?
set -e

[[ -s $aggregate_root/rebuilt-historical-summary.json ]]
[[ -s $aggregate_root/rebuilt-historical-summary.tsv ]]
/usr/bin/printf '%s\n' "$aggregate_rc" > "$aggregate_root/aggregate-exit-code.txt"
(
    cd "$aggregate_root"
    /usr/bin/find . -type f ! -name result-files.sha256 -printf '%P\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$aggregate_root/result-files.sha256"
/usr/bin/chmod -R a-w "$aggregate_root"
/usr/bin/cat "$aggregate_root/rebuilt-historical-summary.json"
exit "$aggregate_rc"
