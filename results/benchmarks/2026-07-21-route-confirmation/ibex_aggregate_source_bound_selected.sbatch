#!/bin/bash
# Aggregate the immutable 592-row source-bound replay. This job runs only
# after the selected array has ended and fails unless all 589 solve claims
# have fresh accepted evidence.
#SBATCH --job-name=km-source-selected-aggregate
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "selected aggregation failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_source_selected_aggregate_env_i_v1__
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
selected_array_job_id=49245587
result_root=$routing_root/source-bound-selected-$selected_array_job_id
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]

aggregator=$submit_dir/aggregate_route_confirmation.py
aggregator_sha256=885e2b0b1d8c851e17e83508b309a79834c678a66ee4f406b171984bf6412ad2
registry=$submit_dir/ontology-solve-routes-source-bound.tsv
registry_sha256=9515703a4343782ebcae3ba414390a1b063f91c0e119af412bdbad0b56ddd72b
selected_driver_sha256=672678599c0db07b2d0ed62a1afe1304783a84e8220cc1b96eaa83b47502b53d

expected_submit_entries=(
    aggregate_route_confirmation.py
    ibex_aggregate_source_bound_selected.sbatch
    ontology-solve-routes-source-bound.tsv
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
[[ $(/usr/bin/sha256sum "$aggregator" | /usr/bin/awk '{print $1}') == "$aggregator_sha256" ]]
[[ $(/usr/bin/sha256sum "$registry" | /usr/bin/awk '{print $1}') == "$registry_sha256" ]]
[[ -d $result_root && ! -L $result_root ]]
[[ ! -e $result_root/selected-summary.json ]]
[[ ! -e $result_root/selected-summary.tsv ]]

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    /usr/bin/python3 -I "$aggregator" \
        --registry "$registry" \
        --result-dir "$result_root" \
        --summary-json "$result_root/selected-summary.json" \
        --summary-tsv "$result_root/selected-summary.tsv" \
        --expected-registry-sha256 "$registry_sha256" \
        --expected-slurm-array-job-id "$selected_array_job_id" \
        --expected-timeout 240 \
        --expected-memcap-mb 20480 \
        --expected-binary-sha256 e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30 \
        --expected-source-manifest-sha256 4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794 \
        --expected-build-receipt-sha256 c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda \
        --expected-km-runtime-sha256 ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5 \
        --expected-ldd-sha256 2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5 \
        --expected-validator-sha256 017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08 \
        --expected-validation-driver-sha256 "$selected_driver_sha256" \
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

/usr/bin/chmod 0444 "$result_root/selected-summary.json" "$result_root/selected-summary.tsv"
