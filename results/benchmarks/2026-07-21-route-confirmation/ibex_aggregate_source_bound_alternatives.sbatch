#!/bin/bash
# Aggregate the completed 10,755-row current alternative-route campaign.
# Negative route outcomes are retained as terminal experiments; only exact
# full-IRI matches count as confirmed solve routes.
#SBATCH --job-name=km-source-alt-aggregate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "alternative aggregation failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_source_alternative_aggregate_env_i_v1__
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
campaign_tag=20260721-02-capsule10
campaign_root=$routing_root/source-bound-alternatives-$campaign_tag
manifest_sha256=e863cdd77d10bf17e68afbd53126a55741f95c135ba9aceb53c94caa37a743f2
validation_driver_sha256=23593f31dfbba5b209bfc516a913a0d72ed9d6e9005343d495003e520b76a7e7
wave_coordinator_sha256=b82f05c690ae3adfc54c5707d040a0c5ec827beacbc339ed2da1bf8251cfd394
validation_stage=$routing_root/validation-drivers/sha256-$validation_driver_sha256
manifest=$validation_stage/alternative-route-manifest-source-bound.tsv

submit_dir=$(/usr/bin/readlink -f "$SLURM_SUBMIT_DIR")
driver=$(/usr/bin/readlink -f "${BASH_SOURCE[0]}")
driver_sha256=$(/usr/bin/sha256sum "$driver" | /usr/bin/awk '{print $1}')
[[ $(/usr/bin/basename "$submit_dir") == sha256-$driver_sha256 ]]
[[ $submit_dir == */routing_20260715/validation-drivers/sha256-$driver_sha256 ]]
aggregator=$submit_dir/aggregate_alternative_confirmation.py
aggregator_sha256=$(/usr/bin/sha256sum "$aggregator" | /usr/bin/awk '{print $1}')

expected_submit_entries=(
    aggregate_alternative_confirmation.py
    ibex_aggregate_source_bound_alternatives.sbatch
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
for path in "$driver" "$aggregator" "$manifest"; do
    [[ -s $path && ! -L $path ]]
done
[[ $(/usr/bin/sha256sum "$manifest" | /usr/bin/awk '{print $1}') == "$manifest_sha256" ]]
[[ -d $campaign_root && ! -L $campaign_root ]]

# The original 1 GiB finalizer (job 49269392) retained every JSON document and
# was OOM-killed. It never produced a claim. This bounded-memory aggregator
# independently checks all 10,755 rows and supersedes that failed metadata job.
failed_finalizer_log=$routing_root/slurm-km-alt-submit-49269392.out
[[ -s $failed_finalizer_log && ! -L $failed_finalizer_log ]]

output_root=$routing_root/source-bound-alternative-aggregation-$SLURM_JOB_ID
[[ ! -e $output_root ]]
/usr/bin/mkdir -m 0755 "$output_root"
wave_manifest=$output_root/wave-submissions.sha256
wave_job_args=()
for wave in 0 1 2 3 4 5 6; do
    receipt=$campaign_root/wave-control/wave-$wave.lock/submission.json
    [[ -s $receipt && ! -L $receipt ]]
    /usr/bin/sha256sum "$receipt" >> "$wave_manifest"
    array_job_id=$(/usr/bin/python3 -I - "$receipt" "$wave" \
        "$campaign_tag" "$manifest_sha256" "$validation_driver_sha256" \
        "$wave_coordinator_sha256" <<'PY'
import json
from pathlib import Path
import sys

receipt = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
wave = int(sys.argv[2])
expected = {
    "schema_version": 1,
    "status": "wave_submitted",
    "wave_index": wave,
    "campaign_tag": sys.argv[3],
    "manifest_sha256": sys.argv[4],
    "validation_driver_sha256": sys.argv[5],
    "wave_coordinator_sha256": sys.argv[6],
}
failed = [key for key, value in expected.items() if receipt.get(key) != value]
if failed:
    raise SystemExit(f"wave {wave} receipt mismatch: {failed}")
job_id = str(receipt.get("array_job_id", ""))
if not job_id.isdigit():
    raise SystemExit(f"wave {wave} lacks a numeric array job ID")
print(job_id)
PY
    )
    wave_job_args+=(--expected-slurm-array-job-id "$array_job_id")
done

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    /usr/bin/python3 -I "$aggregator" \
        --manifest "$manifest" \
        --result-dir "$campaign_root" \
        --summary-json "$output_root/alternative-summary.json" \
        --summary-tsv "$output_root/alternative-summary.tsv" \
        --expected-manifest-sha256 "$manifest_sha256" \
        --expected-binary-sha256 e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30 \
        --expected-source-manifest-sha256 4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794 \
        --expected-build-receipt-sha256 c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda \
        --expected-konclude-sha256 e8dd5373d4606a1c9dbab0896b5939124ef7997781f15aea0d6f5fc6fd4cf0f4 \
        --expected-konclude-runtime-sha256 b26f41184a6a414e13213dbd0059fd8ba49a229f7017f113f5d6bac34ecab123 \
        --expected-konclude-build-receipt-sha256 e79b9ef8fe8b46122bb04e6749a876c4500da813f19795fbe888192ec1566651 \
        --expected-konclude-source-manifest-sha256 a188a16ac440259e58c289ea766cd457a402e7c85ceb6c3e5b11a7ca08b116d2 \
        --expected-konclude-build-driver-sha256 f10514068f31c14da2187f8ebe14dd400f39b36a310a84f6cac811a20d14c6d5 \
        --expected-selected-registry-sha256 9515703a4343782ebcae3ba414390a1b063f91c0e119af412bdbad0b56ddd72b \
        --expected-selected-summary-sha256 82b300115a0cc7ee4d459065b9f3733aa76473444824b91be4948f5472e7e8da \
        --expected-selected-result-manifest-sha256 a855926e03b43e53f543e431f26cb5581b89314eb25251768e37aa7c7ad629fd \
        "${wave_job_args[@]}" \
        --expected-timeout 240 \
        --expected-memcap-mb 20480 \
        --expected-validator-sha256 72952c039ea7807796e7df948b9bc0e96e7eb305b6f5d844ff80a5b7ea5c1390 \
        --expected-shared-validator-sha256 017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08 \
        --expected-validation-driver-sha256 "$validation_driver_sha256" \
        --expected-selected-driver-sha256 672678599c0db07b2d0ed62a1afe1304783a84e8220cc1b96eaa83b47502b53d \
        --expected-runner-sha256 2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c \
        --expected-fingerprint-tool-sha256 b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6 \
        --expected-km-runtime-sha256 ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5 \
        --expected-ldd-sha256 2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5 \
        --strict

/usr/bin/python3 -I - "$output_root" "$campaign_root" "$driver_sha256" \
    "$aggregator_sha256" "$manifest_sha256" "$failed_finalizer_log" \
    "$wave_manifest" "$SLURM_JOB_ID" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

root = Path(sys.argv[1])
summary = root / "alternative-summary.json"
payload = json.loads(summary.read_text(encoding="utf-8"))
if payload.get("campaign_complete") is not True:
    raise SystemExit("aggregator did not certify a complete campaign")
receipt = {
    "schema_version": 1,
    "status": "verified_complete",
    "campaign_root": sys.argv[2],
    "aggregation_driver_sha256": sys.argv[3],
    "aggregator_sha256": sys.argv[4],
    "manifest_sha256": sys.argv[5],
    "superseded_finalizer_job_id": "49269392",
    "superseded_finalizer_status": "metadata_oom_no_claim",
    "superseded_finalizer_log_sha256": sha256(Path(sys.argv[6])),
    "wave_submission_manifest_sha256": sha256(Path(sys.argv[7])),
    "summary_sha256": sha256(summary),
    "summary_tsv_sha256": sha256(root / "alternative-summary.tsv"),
    "slurm_job_id": sys.argv[8],
}
(root / "aggregation-receipt.json").write_text(
    json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
print(json.dumps(receipt, sort_keys=True))
PY

(
    cd "$output_root"
    /usr/bin/find . -type f ! -name result-files.sha256 -printf '%P\0' \
        | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
) > "$output_root/result-files.sha256"
/usr/bin/chmod -R a-w "$output_root"
/usr/bin/cat "$output_root/alternative-summary.json"
