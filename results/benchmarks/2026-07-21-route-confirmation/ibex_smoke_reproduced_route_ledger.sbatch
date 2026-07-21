#!/usr/bin/env bash
# Developmental smoke test for the selected + exact-source ledger join.
# The final evidence ledger additionally supplies the complete alternative replay.
#SBATCH --job-name=km-ledger-smoke
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=2G
#SBATCH --output=/ibex/user/hohndor/km/routing_20260715/slurm-km-ledger-smoke-%j.out

set -euo pipefail
trap 'rc=$?; /usr/bin/printf "ledger smoke failed: line=%s rc=%s\n" "$LINENO" "$rc" >&2' ERR

submit_dir=$SLURM_SUBMIT_DIR
generator=$submit_dir/generate_reproduced_route_ledger.py
generator_sha256=174eb9e2fd715bbc9a6b8d66f059372adb34280fcb2158318b8b28499c78f9ec
[[ -s $generator && ! -L $generator ]]
[[ $(/usr/bin/sha256sum "$generator" | /usr/bin/awk '{print $1}') == "$generator_sha256" ]]

routing_root=/ibex/scratch/hohndor/km/routing_20260715
selected_root=$routing_root/source-bound-selected-49245587
selected_stage=/ibex/user/hohndor/km/routing_20260715/validation-drivers/sha256-8f78e08539fcfd9b0928480afd7dbfbad78ebdd346e34a3704074c540a37e573
historical_root=$routing_root/source-bound-rebuilt-historical-49260043
historical_aggregate=$routing_root/source-bound-rebuilt-historical-aggregation-49260670
historical_stage=/ibex/user/hohndor/km/routing_20260715/validation-drivers/sha256-eb29cc0095c047c5cf9056d4a5aeaab6651c9a51b0779c6f3d36ccfe82a01240
output_root=$routing_root/reproduced-route-ledger-smoke-$SLURM_JOB_ID
[[ ! -e $output_root ]]
/usr/bin/mkdir -m 0755 "$output_root"

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C PYTHONHASHSEED=0 \
    /usr/bin/python3 -I "$generator" \
    --registry "$selected_stage/ontology-solve-routes-source-bound.tsv" \
    --selected-result-dir "$selected_root" \
    --selected-summary-json "$selected_root/selected-summary.json" \
    --selected-summary-sha256 82b300115a0cc7ee4d459065b9f3733aa76473444824b91be4948f5472e7e8da \
    --selected-aggregator "$selected_stage/aggregate_route_confirmation.py" \
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
    --expected-alternative-aggregator-sha256 75e5203e1f98ce906ae5095ba8894489d8d50c237ca5ad812cc083e01bd8cf61 \
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
    --output "$output_root/reproduced-route-ledger-smoke.tsv"

/usr/bin/python3 -I - "$output_root" "$generator" "$SLURM_JOB_ID" <<'PY'
import csv
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
generator = Path(sys.argv[2])
ledger = root / "reproduced-route-ledger-smoke.tsv"
with ledger.open(newline="", encoding="utf-8") as handle:
    rows = list(csv.DictReader(handle, delimiter="\t"))
counts = {}
for row in rows:
    counts[row["current_state"]] = counts.get(row["current_state"], 0) + 1
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
receipt = {
    "schema_version": 1,
    "status": "developmental_selected_plus_exact_source_smoke",
    "rows": len(rows),
    "states": dict(sorted(counts.items())),
    "generator_sha256": sha(generator),
    "ledger_sha256": sha(ledger),
    "slurm_job_id": sys.argv[3],
}
(root / "receipt.json").write_text(
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
