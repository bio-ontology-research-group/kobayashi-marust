#!/bin/bash
# Derive the route/correctness/performance table from accepted route evidence
# and the repaired frozen external-baseline matrix.
# This job reads metadata only; it does not execute a reasoner.
#SBATCH --job-name=km-route-perf
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=1G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "route performance build failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_route_performance_env_i_v1__
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
submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
builder=$submit_dir/build_route_performance.py
builder_sha256=a76d1618dbfe54b567a87ae446317da68e96eb4db8612de8a49564fb8785d07a
expected_submit_entries=(
    build_route_performance.py
    ibex_build_route_performance.sbatch
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
[[ -s $builder && ! -L $builder ]]
[[ $(/usr/bin/sha256sum "$builder" | /usr/bin/awk '{print $1}') == "$builder_sha256" ]]

ledger=$routing_root/reproduced-route-ledger-49272959/reproduced-route-ledger.tsv
ledger_sha256=7db5b5b3c645cb2f37e515d215808ef3de499249c7a2d3fd22ec50771e64f354
[[ -s $ledger && ! -L $ledger ]]
[[ $(/usr/bin/sha256sum "$ledger" | /usr/bin/awk '{print $1}') == "$ledger_sha256" ]]
baseline_results=$routing_root/matrix-results-c229366f
[[ -d $baseline_results && ! -L $baseline_results ]]

output_root=$routing_root/reproduced-route-performance-$SLURM_JOB_ID
[[ ! -e $output_root ]]
/usr/bin/mkdir -m 0755 "$output_root"
table=$output_root/ontology-route-performance.tsv
summary=$output_root/route-performance-summary.json
receipt=$output_root/route-performance-receipt.json

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    /usr/bin/python3 -I "$builder" \
    --ledger "$ledger" \
    --baseline-results "$baseline_results" \
    --output-tsv "$table" \
    --output-summary "$summary" \
    --output-receipt "$receipt" \
    --slurm-job-id "$SLURM_JOB_ID" \
    --aggregation-driver-sha256 "$driver_sha256"

/usr/bin/python3 -I - "$table" "$summary" "$receipt" "$builder" \
    "$driver" "$SLURM_JOB_ID" <<'PY'
import csv
import hashlib
import json
from pathlib import Path
import sys

table, summary, receipt, builder, driver = map(Path, sys.argv[1:6])
job_id = sys.argv[6]

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

summary_data = json.loads(summary.read_text(encoding="utf-8"))
receipt_data = json.loads(receipt.read_text(encoding="utf-8"))
with table.open(newline="", encoding="utf-8") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))
assert len(rows) == 592
assert len({row["ontology"] for row in rows}) == 592
assert sum(row["km_sound"] == "yes" and row["km_complete"] == "yes" for row in rows) == 589
assert sum(row["konclude_sound"] == "yes" and row["konclude_complete"] == "yes" for row in rows) == 587
assert sum(row["hermit_sound"] == "yes" and row["hermit_complete"] == "yes" for row in rows) == 551
assert sum(row["elk_sound"] == "yes" and row["elk_complete"] == "yes" for row in rows) == 531
assert sum(row["km_state"] == "not_currently_verified_solved" for row in rows) == 3
assert all(row["km_wall_s"] and row["km_peak_mb"] for row in rows if row["km_status"] == "ok")
assert all(row["konclude_wall_s"] and row["konclude_peak_mb"] for row in rows)
assert all(row["hermit_wall_s"] and row["hermit_peak_mb"] for row in rows)
assert all(row["elk_wall_s"] and row["elk_peak_mb"] for row in rows)
assert summary_data["status"] == "verified_route_correctness_performance"
assert receipt_data["status"] == "verified_route_correctness_performance_receipt"
assert summary_data["slurm_job_id"] == receipt_data["slurm_job_id"] == job_id
assert receipt_data["table_sha256"] == summary_data["table_sha256"] == sha256(table)
assert receipt_data["summary_sha256"] == sha256(summary)
assert receipt_data["builder_sha256"] == sha256(builder)
assert receipt_data["aggregation_driver_sha256"] == sha256(driver)
assert receipt_data["rows"] == 592
assert receipt_data["reproduced"] == 589
assert receipt_data["exact_full_iri"] == 587
assert receipt_data["adjudicated_inconsistent"] == 2
assert receipt_data["sound_and_complete"] == {
    "elk": 531, "hermit": 551, "km": 589, "konclude": 587
}
print(json.dumps(receipt_data, sort_keys=True))
PY

(
    cd "$output_root"
    /usr/bin/sha256sum \
        ontology-route-performance.tsv \
        route-performance-receipt.json \
        route-performance-summary.json \
        > result-files.sha256
)
/usr/bin/chmod 0444 \
    "$table" "$summary" "$receipt" "$output_root/result-files.sha256"
/usr/bin/chmod 0555 "$output_root"
