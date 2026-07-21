#!/bin/bash
# Reasoner-free audit of datatype influence in the exact saved 10621 TInput.
# This is diagnostic only and cannot emit route-acceptance evidence.
#SBATCH --job-name=km10621-dt-audit
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "datatype audit failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

sentinel=__km10621_dt_audit_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    exec /usr/bin/env -i \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        /bin/bash "$script_path" "$sentinel"
fi
if [[ $# -ne 1 || $1 != "$sentinel" ]]; then
    echo "invalid clean-environment sentinel" >&2
    exit 2
fi
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
expected_submit_dir=$(/usr/bin/readlink -f \
    "$routing_root/validation-drivers/sha256-$driver_sha256")
[[ $submit_dir == "$expected_submit_dir" ]]
[[ $(/usr/bin/find "$submit_dir" -maxdepth 1 -type f -printf . | /usr/bin/wc -c) -eq 2 ]]

auditor=$submit_dir/audit_10621_datatype_tinput.py
auditor_sha256=9353e3a2f3ab61b8ddebeb2f8483c73bc751f10c5c2ba278a7872eb123be72a4
tin=$routing_root/10621-reproducible-06-49218992/ore_ont_10621.ht-bridge.tinput.json
tin_sha256=2dff5d801d4b9460787802a02a100168dbc1b8008e8cdad32870d2a959250cbb
output=$routing_root/10621-reproducible-06-49218992/datatype-audit-$SLURM_JOB_ID.json

[[ ! -e $output ]]
[[ $(/usr/bin/sha256sum "$auditor" | /usr/bin/awk '{print $1}') == "$auditor_sha256" ]]
[[ $(/usr/bin/sha256sum "$tin" | /usr/bin/awk '{print $1}') == "$tin_sha256" ]]
/usr/bin/python3 "$auditor" \
    --tin "$tin" \
    --tin-sha256 "$tin_sha256" \
    --output "$output"
[[ $(/usr/bin/python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["status"])' "$output") == analyzed ]]
/usr/bin/chmod 0444 "$output"
/usr/bin/sha256sum "$driver" "$auditor" "$tin" "$output"
