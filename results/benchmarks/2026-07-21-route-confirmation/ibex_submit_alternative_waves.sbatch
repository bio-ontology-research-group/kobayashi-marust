#!/bin/bash
# Submit the 10,755 source-bound alternative-route validations in scheduler-
# quota-sized waves. Each successor starts only after every record from the
# preceding wave exists and is terminal.
#SBATCH --job-name=km-alt-submit
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=512M
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "wave coordinator failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_alternative_wave_env_i_v1__
if [[ $# -eq 0 ]]; then
    script_path=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
    optional_slurm=()
    if [[ -n ${SLURM_TMPDIR:-} ]]; then
        optional_slurm+=(SLURM_TMPDIR="$SLURM_TMPDIR")
    fi
    exec /usr/bin/env -i \
        WAVE_INDEX="${WAVE_INDEX:?submit with WAVE_INDEX=0}" \
        CAMPAIGN_TAG="${CAMPAIGN_TAG:?submit with CAMPAIGN_TAG}" \
        SLURM_JOB_ID="${SLURM_JOB_ID:?missing Slurm job identifier}" \
        SLURM_CPUS_PER_TASK="${SLURM_CPUS_PER_TASK:?missing Slurm CPU count}" \
        SLURM_SUBMIT_DIR="${SLURM_SUBMIT_DIR:?missing Slurm submit directory}" \
        "${optional_slurm[@]}" \
        /bin/bash "$script_path" "$clean_sentinel"
fi
[[ $# -eq 1 && $1 == "$clean_sentinel" ]]
shift
while IFS= read -r exported_name; do
    case "$exported_name" in
        WAVE_INDEX|CAMPAIGN_TAG|SLURM_JOB_ID|SLURM_CPUS_PER_TASK|\
        SLURM_SUBMIT_DIR|SLURM_TMPDIR|PWD|SHLVL|_) ;;
        *) echo "unexpected variable after env -i: $exported_name" >&2; exit 2 ;;
    esac
done < <(compgen -e)
[[ $SLURM_CPUS_PER_TASK == 1 ]]
[[ $WAVE_INDEX =~ ^[0-7]$ ]]
[[ $CAMPAIGN_TAG =~ ^[a-z0-9-]+$ ]]

export PATH=/usr/bin:/bin
export LC_ALL=C
export PYTHONHASHSEED=0

routing_root=/ibex/scratch/hohndor/km/routing_20260715
driver_sha256=23593f31dfbba5b209bfc516a913a0d72ed9d6e9005343d495003e520b76a7e7
manifest_sha256=e863cdd77d10bf17e68afbd53126a55741f95c135ba9aceb53c94caa37a743f2
sbatch=/opt/slurm/install/slurm-25.05.7/f3574d87bebe06b19e50c04c321eeb9798c4ed7c/RedHat-9/bin/sbatch
sbatch_sha256=eeaff54e4049a603295ebe19265bad055ac1faae425ad0c1e22e63ac6904a46d
driver_stage=/ibex/user/hohndor/km/routing_20260715/validation-drivers/sha256-$driver_sha256
validation_driver=$driver_stage/ibex_confirm_source_bound_alternatives.sbatch
manifest=$driver_stage/alternative-route-manifest-source-bound.tsv
script=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
script_sha256=$(/usr/bin/sha256sum "$script" | /usr/bin/awk '{print $1}')
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
[[ $(/usr/bin/basename "$submit_dir") == sha256-$script_sha256 ]]
[[ $(/usr/bin/sha256sum \
    "$submit_dir/ibex_submit_alternative_waves.sbatch" \
    | /usr/bin/awk '{print $1}') == "$script_sha256" ]]
[[ $(/usr/bin/sha256sum "$validation_driver" | /usr/bin/awk '{print $1}') == "$driver_sha256" ]]
[[ $(/usr/bin/sha256sum "$manifest" | /usr/bin/awk '{print $1}') == "$manifest_sha256" ]]
[[ $(/usr/bin/sha256sum "$sbatch" | /usr/bin/awk '{print $1}') == "$sbatch_sha256" ]]

result_root=$routing_root/source-bound-alternatives-$CAMPAIGN_TAG
control_root=$result_root/wave-control
/usr/bin/mkdir -p "$control_root"
lock_directory=$control_root/wave-$WAVE_INDEX.lock
if ! /usr/bin/mkdir "$lock_directory"; then
    echo "wave $WAVE_INDEX was already coordinated: $lock_directory" >&2
    exit 2
fi

wave_starts=(0 1900 3800 5700 7600 9500 10000)
wave_ends=(1899 3799 5699 7599 9499 9999 10754)

verify_terminal_range() {
    local first=$1
    local last=$2
    /usr/bin/python3 -I - "$result_root" "$first" "$last" <<'PY'
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
first = int(sys.argv[2])
last = int(sys.argv[3])
observed = set()
nonterminal = []
for path in sorted((root / "alternative-results").glob("*/*.json")):
    record = json.loads(path.read_text(encoding="utf-8"))
    index = record.get("task_index")
    if isinstance(index, int) and first <= index <= last:
        if index in observed:
            raise SystemExit(f"duplicate terminal record for row {index}")
        observed.add(index)
        if (
            record.get("phase") != "complete"
            or record.get("confirmation_status") in (None, "running")
        ):
            nonterminal.append(index)
missing = sorted(set(range(first, last + 1)) - set(observed))
nonterminal.sort()
if missing or nonterminal:
    raise SystemExit(
        f"wave evidence incomplete: missing={missing[:20]} "
        f"nonterminal={nonterminal[:20]}"
    )
print(json.dumps({"first": first, "last": last, "records": len(observed)}))
PY
}

if (( WAVE_INDEX == 0 )); then
    if /usr/bin/find "$result_root/alternative-results" -type f -name '*.json' \
            -print -quit 2>/dev/null | /usr/bin/grep -q .; then
        echo "campaign already contains alternative results" >&2
        exit 2
    fi
else
    previous=$((WAVE_INDEX - 1))
    verify_terminal_range "${wave_starts[$previous]}" "${wave_ends[$previous]}" \
        > "$lock_directory/previous-wave-check.json"
fi

if (( WAVE_INDEX == 7 )); then
    verify_terminal_range 0 10754 > "$lock_directory/all-rows-check.json"
    /usr/bin/python3 -I - "$result_root" "$lock_directory/final.json" \
        "$script_sha256" "$driver_sha256" "$manifest_sha256" \
        "$SLURM_JOB_ID" <<'PY'
from collections import Counter
import json
import os
from pathlib import Path
import sys

root = Path(sys.argv[1])
output = Path(sys.argv[2])
statuses = Counter()
indices = set()
confirmed = 0
result_records = 0
for path in sorted((root / "alternative-results").glob("*/*.json")):
    record = json.loads(path.read_text(encoding="utf-8"))
    result_records += 1
    statuses[record.get("confirmation_status", "missing")] += 1
    confirmed += record.get("confirmed") is True
    indices.add(record.get("task_index"))
summary = {
    "schema_version": 1,
    "status": "all_rows_terminal",
    "result_records": result_records,
    "unique_task_indices": len(indices),
    "confirmation_statuses": dict(sorted(statuses.items())),
    "confirmed": confirmed,
    "wave_coordinator_sha256": sys.argv[3],
    "validation_driver_sha256": sys.argv[4],
    "manifest_sha256": sys.argv[5],
    "finalizer_slurm_job_id": sys.argv[6],
}
temporary = output.with_suffix(".tmp")
temporary.write_text(
    json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
os.replace(temporary, output)
print(json.dumps(summary, sort_keys=True))
PY
    /usr/bin/chmod 0444 "$lock_directory"/*.json
    /usr/bin/chmod 0555 "$lock_directory"
    exit 0
fi

first=${wave_starts[$WAVE_INDEX]}
last=${wave_ends[$WAVE_INDEX]}
if (( WAVE_INDEX < 6 )); then
    task_offset=0
    array_spec=${first}-${last}%48
else
    task_offset=10000
    array_spec=0-754%48
fi

array_submission=$(
    cd "$driver_stage"
    "$sbatch" --parsable \
        --export=TASK_OFFSET=$task_offset,CAMPAIGN_TAG=$CAMPAIGN_TAG \
        --array="$array_spec" \
        "$validation_driver"
)
array_job_id=${array_submission%%;*}
[[ $array_job_id =~ ^[0-9]+$ ]]

next_wave=$((WAVE_INDEX + 1))
next_submission=$(
    cd "$submit_dir"
    "$sbatch" --parsable --dependency=afterany:$array_job_id \
        --export=WAVE_INDEX=$next_wave,CAMPAIGN_TAG=$CAMPAIGN_TAG \
        "$script"
)
next_coordinator_job_id=${next_submission%%;*}
[[ $next_coordinator_job_id =~ ^[0-9]+$ ]]

/usr/bin/python3 -I - "$lock_directory/submission.json" \
    "$WAVE_INDEX" "$first" "$last" "$task_offset" "$array_spec" \
    "$array_job_id" "$next_coordinator_job_id" "$SLURM_JOB_ID" \
    "$CAMPAIGN_TAG" "$script_sha256" "$driver_sha256" \
    "$manifest_sha256" <<'PY'
import json
import os
from pathlib import Path
import sys

output = Path(sys.argv[1])
record = {
    "schema_version": 1,
    "status": "wave_submitted",
    "wave_index": int(sys.argv[2]),
    "first_row": int(sys.argv[3]),
    "last_row": int(sys.argv[4]),
    "task_offset": int(sys.argv[5]),
    "array_specification": sys.argv[6],
    "array_job_id": sys.argv[7],
    "next_coordinator_job_id": sys.argv[8],
    "coordinator_job_id": sys.argv[9],
    "campaign_tag": sys.argv[10],
    "wave_coordinator_sha256": sys.argv[11],
    "validation_driver_sha256": sys.argv[12],
    "manifest_sha256": sys.argv[13],
}
temporary = output.with_suffix(".tmp")
temporary.write_text(
    json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
os.replace(temporary, output)
print(json.dumps(record, sort_keys=True))
PY
/usr/bin/chmod 0444 "$lock_directory"/*.json
/usr/bin/chmod 0555 "$lock_directory"
