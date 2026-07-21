#!/bin/bash
# Reasoner-free structural diagnosis of the exact TInput rejected by final
# capsule-08 task 49227162_1. This runs only on an IBEX compute node and cannot
# constitute route-acceptance evidence.
#SBATCH --job-name=km10621-final08-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:04:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "TInput audit failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

sentinel=__km10621_final08_audit_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$sentinel"
fi
[[ $# -eq 1 && $1 == "$sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        SLURM_JOB_ID|SLURM_SUBMIT_DIR|PWD|SHLVL|_) ;;
        *) echo "unexpected exported variable: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

routing_root=/ibex/scratch/hohndor/km/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]

expected_entries=(
    audit_10621_datatype_roles.py
    ibex_audit_10621_final08_datatype_roles.sbatch
)
mapfile -t actual_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_entries[@]} -eq ${#expected_entries[@]} ]]
for index in "${!expected_entries[@]}"; do
    [[ ${actual_entries[$index]} == "${expected_entries[$index]}" ]]
    [[ -f $submit_dir/${actual_entries[$index]} \
        && ! -L $submit_dir/${actual_entries[$index]} ]]
done

auditor=$submit_dir/audit_10621_datatype_roles.py
auditor_sha256=5223925dedf257886ffe250555b55ca5b0a7dd35e2b058b09f15ccc4f06a0ee6
tin=$routing_root/final-targeted08-49227162-1/ore_ont_10621.ht-bridge.tinput.json
tin_sha256=206ffdc237b6c78bf4a19305763004015456278ac94bb3dad022f723f72d761b
output=$routing_root/final-targeted08-49227162-1/datatype-role-audit-$SLURM_JOB_ID.json

[[ ! -e $output ]]
[[ $(/usr/bin/sha256sum "$auditor" | /usr/bin/awk '{print $1}') == "$auditor_sha256" ]]
[[ $(/usr/bin/sha256sum "$tin" | /usr/bin/awk '{print $1}') == "$tin_sha256" ]]
/usr/bin/python3 -I "$auditor" \
    --tin "$tin" \
    --tin-sha256 "$tin_sha256" \
    --output "$output"
/usr/bin/chmod 0444 "$output"
/usr/bin/sha256sum "$driver" "$auditor" "$tin" "$output"
