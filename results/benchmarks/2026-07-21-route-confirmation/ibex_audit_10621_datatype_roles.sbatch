#!/bin/bash
# Structural audit of role-local datatype isolation in the exact saved 10621
# TInput.  This never executes a reasoner and must run on a compute node.
#SBATCH --job-name=km10621-dtroles
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:03:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail

clean_sentinel=__km10621_dtroles_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

routing_root=/ibex/scratch/hohndor/km/routing_20260715
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $submit_dir == */validation-drivers/sha256-$driver_sha256 ]]
auditor=$submit_dir/audit_10621_datatype_roles.py
auditor_sha256=5223925dedf257886ffe250555b55ca5b0a7dd35e2b058b09f15ccc4f06a0ee6
[[ $(/usr/bin/sha256sum "$auditor" | /usr/bin/awk '{print $1}') == "$auditor_sha256" ]]

run_root=$routing_root/10621-reproducible-06-49218992
tin=$run_root/ore_ont_10621.ht-bridge.tinput.json
tin_sha256=2dff5d801d4b9460787802a02a100168dbc1b8008e8cdad32870d2a959250cbb
output=$run_root/datatype-role-audit-$SLURM_JOB_ID.json
[[ ! -e $output ]]
/usr/bin/python3 "$auditor" \
    --tin "$tin" \
    --tin-sha256 "$tin_sha256" \
    --output "$output"
/usr/bin/chmod 0444 "$output"
/usr/bin/sha256sum "$output"
