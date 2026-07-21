#!/bin/bash
# Produce the final 592-row ledger from source-bound evidence only.
# Historical opaque executables are never inputs to this job.
#SBATCH --job-name=km-route-ledger
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=4G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm-%x-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "reproduced route ledger failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

clean_sentinel=__km_reproduced_route_ledger_env_i_v1__
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
generator=$submit_dir/generate_reproduced_route_ledger.py
generator_sha256=9e8b8580216c2f3388dd12eb4e9365bd9d67c669bff2baddf95464660b1c84b2
expected_submit_entries=(
    generate_reproduced_route_ledger.py
    ibex_generate_reproduced_route_ledger.sbatch
)
mapfile -t actual_submit_entries < <(
    /usr/bin/find "$submit_dir" -mindepth 1 -maxdepth 1 -printf '%f\n' \
        | /usr/bin/sort
)
[[ ${#actual_submit_entries[@]} -eq ${#expected_submit_entries[@]} ]]
for index in "${!expected_submit_entries[@]}"; do
    [[ ${actual_submit_entries[$index]} == "${expected_submit_entries[$index]}" ]]
done
[[ -s $generator && ! -L $generator ]]
[[ $(/usr/bin/sha256sum "$generator" | /usr/bin/awk '{print $1}') == "$generator_sha256" ]]

selected_root=$routing_root/source-bound-selected-49245587
selected_stage=/ibex/user/hohndor/km/routing_20260715/validation-drivers/sha256-8f78e08539fcfd9b0928480afd7dbfbad78ebdd346e34a3704074c540a37e573
alternative_root=$routing_root/source-bound-alternatives-20260721-02-capsule10
alternative_stage=$routing_root/validation-drivers/sha256-23593f31dfbba5b209bfc516a913a0d72ed9d6e9005343d495003e520b76a7e7
alternative_aggregate=$routing_root/source-bound-alternative-aggregation-49271931
alternative_aggregate_stage=$routing_root/validation-drivers/sha256-b06b880a5f437faf7841d1e02c82855a0e261e9c3b95034f3f59d45625e1010e
exact_result=$routing_root/source-bound-exact-candidates-49271944
exact_registry_root=$routing_root/exact-candidate-replay-registry-20260722-01
exact_capsule_registry_root=$routing_root/exact-candidate-registry-final-20260722-01
exact_aggregate=$routing_root/source-bound-exact-candidate-aggregation-20260722-01
exact_aggregate_stage=$routing_root/validation-drivers/sha256-1a18c4f1d43e6aef148cc012da9075d9882728181ab05b8eefd79e0dbd471710
historical_root=$routing_root/source-bound-rebuilt-historical-49260043
historical_aggregate=$routing_root/source-bound-rebuilt-historical-aggregation-49260670
historical_stage=/ibex/user/hohndor/km/routing_20260715/validation-drivers/sha256-eb29cc0095c047c5cf9056d4a5aeaab6651c9a51b0779c6f3d36ccfe82a01240

output_root=$routing_root/reproduced-route-ledger-$SLURM_JOB_ID
[[ ! -e $output_root ]]
/usr/bin/mkdir -m 0755 "$output_root"
ledger=$output_root/reproduced-route-ledger.tsv

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    /usr/bin/python3 -I "$generator" \
    --registry "$selected_stage/ontology-solve-routes-source-bound.tsv" \
    --selected-result-dir "$selected_root" \
    --selected-summary-json "$selected_root/selected-summary.json" \
    --selected-summary-sha256 82b300115a0cc7ee4d459065b9f3733aa76473444824b91be4948f5472e7e8da \
    --selected-aggregator "$selected_stage/aggregate_route_confirmation.py" \
    --alternative-result-dir "$alternative_root" \
    --alternative-manifest "$alternative_stage/alternative-route-manifest-source-bound.tsv" \
    --alternative-summary-json "$alternative_aggregate/alternative-summary.json" \
    --alternative-summary-sha256 ef008c82b9fca9b2e6349556ac92bb391c4ab8ad5af619c700a6b4b754c40017 \
    --alternative-aggregator "$alternative_aggregate_stage/aggregate_alternative_confirmation.py" \
    --exact-candidate-result-dir "$exact_result" \
    --exact-candidate-registry "$exact_registry_root/exact-candidate-routes.tsv" \
    --exact-candidate-registry-receipt "$exact_registry_root/exact-candidate-routes-receipt.json" \
    --exact-candidate-capsules "$exact_capsule_registry_root/exact-candidate-capsules.tsv" \
    --exact-candidate-capsules-receipt "$exact_capsule_registry_root/exact-candidate-capsules-receipt.json" \
    --exact-candidate-summary-json "$exact_aggregate/exact-candidate-summary.json" \
    --exact-candidate-summary-sha256 262e62584fa788c7689d362636d3d6f936337bcc4d53faa54e4b0da4f9833f50 \
    --exact-candidate-aggregator "$exact_aggregate_stage/aggregate_exact_candidate_confirmation.py" \
    --rebuilt-historical-result-dir "$historical_root" \
    --rebuilt-historical-registry "$historical_stage/rebuilt-historical-routes-source-bound.tsv" \
    --rebuilt-historical-summary-json "$historical_aggregate/rebuilt-historical-summary.json" \
    --rebuilt-historical-summary-sha256 ed3e0468847ac065c5e6c074fb923db0bf26faaf7fa208c9ef1c95bc5bc12d14 \
    --rebuilt-historical-aggregator "$historical_stage/aggregate_route_confirmation.py" \
    --expected-binary-sha256 e8817734877911a45320830324cefdfb1002b411896f5b7982deab31673f6b30 \
    --expected-source-manifest-sha256 4f52e2b8d587f729fb9f84354e8fe1cc5ebb372e6f27b6b109dfea1f8a737794 \
    --expected-build-receipt-sha256 c1ee3dced72ad60757befb820b86f28419e04f9326f19a22193c9aa8635b5fda \
    --expected-km-runtime-sha256 ed5f9de424e1d4140197ade2bceaf0f7c9da2bb6399ce75522d091ba966695d5 \
    --expected-ldd-sha256 2e332feed7fe0d65afca81d83d07f997917c07d5c1f1fd5564e98330e78aa0b5 \
    --expected-selected-validator-sha256 017200614fd91b9a8c3268fe555deba6d68cbabde74f69a8b16b191e8ae53a08 \
    --expected-alternative-validator-sha256 72952c039ea7807796e7df948b9bc0e96e7eb305b6f5d844ff80a5b7ea5c1390 \
    --expected-selected-driver-sha256 672678599c0db07b2d0ed62a1afe1304783a84e8220cc1b96eaa83b47502b53d \
    --expected-alternative-driver-sha256 23593f31dfbba5b209bfc516a913a0d72ed9d6e9005343d495003e520b76a7e7 \
    --expected-runner-sha256 2fed168e0c1e9b2b6f0d27b673121cb6bd75127d83c143a214a044c5da59e37c \
    --expected-fingerprint-tool-sha256 b774bfa5f4238d0608935f1b3829c22fb4becb8282d6d2a3466757f850df25a6 \
    --expected-selected-aggregator-sha256 885e2b0b1d8c851e17e83508b309a79834c678a66ee4f406b171984bf6412ad2 \
    --expected-alternative-aggregator-sha256 3d1f3193a39f410d7020efc21891f08764da1e04fe7c5a439e83c8089519fc11 \
    --expected-alternative-slurm-array-job-id 49250221 \
    --expected-alternative-slurm-array-job-id 49252586 \
    --expected-alternative-slurm-array-job-id 49256781 \
    --expected-alternative-slurm-array-job-id 49259802 \
    --expected-alternative-slurm-array-job-id 49263255 \
    --expected-alternative-slurm-array-job-id 49267716 \
    --expected-alternative-slurm-array-job-id 49269391 \
    --expected-exact-candidate-aggregator-sha256 bcc0775b95a213485c5bf05ec1e53e68a647b04a1d07dca462ac08481f992405 \
    --expected-exact-candidate-registry-generator-sha256 15b7a4ba62c730ffde57f79783c66bce6da7f5b43dd77998742e58970942230c \
    --expected-exact-candidate-capsules-generator-sha256 729212823439e0fb39f66ebd9ed0522672c9df52a6a8eadd5c0bd64169d8d07b \
    --expected-exact-candidate-source-verifier-sha256 a5907b0af2b00d7b530edf0148a3c0aaa1016fe4d96554be2582ea31ce2f3148 \
    --expected-exact-candidate-runtime-driver-sha256 c619a815cc9667fd8c63236c3f33ac7a8c78290a65f4036e2acb235ed3fe0f90 \
    --expected-exact-candidate-validator-sha256 f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc \
    --expected-exact-candidate-driver-sha256 f7335035a808d4a60430738970cf3e2c19d7965fa4501c727b86bae33ed3a321 \
    --expected-exact-candidate-slurm-array-job-id 49271944 \
    --expected-rebuilt-historical-binary-sha256 ced4544f50a988f7a07059195ce38a6fca65f0692998c31dce656f513ad66a57 \
    --expected-rebuilt-historical-source-manifest-sha256 f6b393cbda6448ccd255f1b109385134eed8b441439826b70b2e1ccd0a169537 \
    --expected-rebuilt-historical-build-receipt-sha256 9a6eb331df6b86710862eef62878df082f9160f04104a242580d132ef2434ed1 \
    --expected-rebuilt-historical-test-receipt-sha256 bac2429376aad6ff2409f55b9af6a52ef162e2e6dc5fb0c48c7c6df52111d006 \
    --expected-rebuilt-historical-source-identity-sha256 fa1810baebf9d4af5e2f78d215450ec1211c160f8c85ea00def8000a41b6964e \
    --expected-rebuilt-historical-km-runtime-sha256 8c7fd69fcc25283170d11e2b5d9cd6c6187c9bce56f0fd4ee7654e567cb94d00 \
    --expected-rebuilt-historical-validator-sha256 f7c1d32318c13b8e22e521dfd18fc76f774f51e8c15bde8fc17f8bd8abed30cc \
    --expected-rebuilt-historical-driver-sha256 7337b1ea7c179ca468176ae693c66f00a102f7d39ee22220942aa84bf7fe55b2 \
    --expected-rebuilt-historical-aggregator-sha256 dc122d8cf0778248b1c8acb3124877da0ded6239a4e3d87dc0cd14b3c3ac6f5d \
    --expected-rebuilt-historical-slurm-array-job-id 49260043 \
    --expected-selected-slurm-array-job-id 49245587 \
    --expected-timeout 240 \
    --expected-memcap-mb 20480 \
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
    --evidence-locator-prefix ibex: \
    --require-complete \
    --output "$ledger"

/usr/bin/python3 -I - "$ledger" "$generator" "$driver" \
    "$SLURM_JOB_ID" "$output_root/reproduced-route-ledger-receipt.json" <<'PY'
import csv
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ledger = Path(sys.argv[1])
generator = Path(sys.argv[2])
driver = Path(sys.argv[3])
job_id = sys.argv[4]
output = Path(sys.argv[5])

def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()

with ledger.open(newline="", encoding="utf-8") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))
states = Counter(row["current_state"] for row in rows)
origins = Counter(row["chosen_origin"] or "none" for row in rows)
reproduced = [
    row for row in rows if row["current_state"].startswith("reproduced_")
]
nonclaims = [
    row for row in rows
    if row["current_state"] == "not_a_documented_solve_claim"
]
unexpected = [
    row["ontology"]
    for row in rows
    if not row["current_state"].startswith("reproduced_")
    and row["current_state"] != "not_a_documented_solve_claim"
]

hash_fields = (
    "ontology_sha256",
    "binary_sha256",
    "source_manifest_sha256",
    "build_receipt_sha256",
    "km_runtime_manifest_sha256",
    "ldd_sha256",
    "route_specification_sha256",
    "validator_sha256",
    "validation_driver_sha256",
    "runner_sha256",
    "fingerprint_tool_sha256",
    "km_taxonomy_sha256",
    "reference_taxonomy_sha256",
    "reference_binary_sha256",
    "reference_source_sha256",
    "reference_route_specification_sha256",
    "reference_runtime_manifest_sha256",
    "evidence_sha256",
)
row_failures = {}
for row in reproduced:
    failures = []
    for field in hash_fields:
        if re.fullmatch(r"[0-9a-f]{64}", row.get(field, "")) is None:
            failures.append(field)
    try:
        command = json.loads(row["command_json"])
        reference_command = json.loads(row["reference_command_json"])
    except (KeyError, json.JSONDecodeError):
        command = reference_command = []
    if not isinstance(command, list) or len(command) < 3:
        failures.append("command_json")
    if not isinstance(reference_command, list) or not reference_command:
        failures.append("reference_command_json")
    if row.get("route_observation_policy") not in {
        "runtime-trace", "closed-manual-environment"
    }:
        failures.append("route_observation_policy")
    if not row.get("observed_route_identity"):
        failures.append("observed_route_identity")
    if row.get("reference_kind") not in {
        "konclude_full_ontology", "hermit_full_ontology"
    }:
        failures.append("reference_kind")
    if not row.get("evidence_locator", "").startswith("ibex:"):
        failures.append("evidence_locator")
    try:
        if float(row["timeout_s"]) != 240.0:
            failures.append("timeout_s")
        if int(row["memory_limit_mb"]) != 20480:
            failures.append("memory_limit_mb")
        if int(row["cpus"]) != 16:
            failures.append("cpus")
        if float(row["reference_timeout_s"]) != 240.0:
            failures.append("reference_timeout_s")
        if int(row["reference_memory_limit_mb"]) != 20480:
            failures.append("reference_memory_limit_mb")
    except (KeyError, TypeError, ValueError):
        failures.append("limits")
    if row["chosen_origin"] in {
        "exact_source_candidate_route", "exact_source_historical_route"
    }:
        for field in (
            "source_identity_receipt_sha256", "test_receipt_sha256"
        ):
            if re.fullmatch(r"[0-9a-f]{64}", row.get(field, "")) is None:
                failures.append(field)
    if failures:
        row_failures[row["ontology"]] = sorted(set(failures))

expected_nonclaims = {
    "ore_ont_1194.owl", "ore_ont_4669.owl", "ore_ont_10860.owl"
}
checks = {
    "rows": len(rows) == 592,
    "unique_ontologies": len({row["ontology"] for row in rows}) == 592,
    "reproduced_claims": len(reproduced) == 589,
    "nonclaim_count": len(nonclaims) == 3,
    "nonclaim_identity": {row["ontology"] for row in nonclaims}
    == expected_nonclaims,
    "nonclaim_status": all(
        row["failure_status"] == "not_a_documented_solve_claim"
        and not row["chosen_origin"]
        for row in nonclaims
    ),
    "no_unreproduced_claim": not unexpected,
    "reproduced_row_provenance": not row_failures,
}
if not all(checks.values()):
    raise SystemExit(
        f"ledger receipt checks failed: "
        f"{[key for key, value in checks.items() if not value]}; "
        f"unexpected={unexpected}; row_failures={row_failures}"
    )

receipt = {
    "schema_version": 1,
    "status": "verified_complete_reproduced_route_ledger",
    "rows": len(rows),
    "reproduced_claims": len(reproduced),
    "nonclaims": sorted(row["ontology"] for row in nonclaims),
    "states": dict(sorted(states.items())),
    "chosen_origins": dict(sorted(origins.items())),
    "generator_sha256": sha256(generator),
    "aggregation_driver_sha256": sha256(driver),
    "ledger_sha256": sha256(ledger),
    "selected_summary_sha256": "82b300115a0cc7ee4d459065b9f3733aa76473444824b91be4948f5472e7e8da",
    "alternative_summary_sha256": "ef008c82b9fca9b2e6349556ac92bb391c4ab8ad5af619c700a6b4b754c40017",
    "exact_candidate_summary_sha256": "262e62584fa788c7689d362636d3d6f936337bcc4d53faa54e4b0da4f9833f50",
    "rebuilt_historical_summary_sha256": "ed3e0468847ac065c5e6c074fb923db0bf26faaf7fa208c9ef1c95bc5bc12d14",
    "slurm_job_id": job_id,
    "checks": checks,
}
output.write_text(
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
/usr/bin/cat "$output_root/reproduced-route-ledger-receipt.json"
