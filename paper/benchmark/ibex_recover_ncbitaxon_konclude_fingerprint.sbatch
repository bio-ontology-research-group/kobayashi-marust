#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=konclude-ncbitaxon-fingerprint-recovery
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/konclude-ncbitaxon-recovery-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
km_root=/ibex/scratch/hohndor/km
recovery=$root/runner-tools/recover_konclude_fingerprint.py
fingerprinter=$root/runner-tools/fingerprint_km_json_sparse.py.next
validator=$root/runner-tools/validate_result.py.next
runner=$root/runner-tools/run_native_one.py
runtime_root=$km_root/routing_20260715/konclude-oracle-builds/konclude-v0.7.0-1138-build-20260721-03
runtime=$runtime_root/Konclude-build-a
result=$root/current-results/konclude/ncbitaxon.result.json
taxonomy=$root/current-results/konclude/ncbitaxon.taxonomy.owlxml
source=$root/obo-snapshot/merged/ncbitaxon.ofn
runtime_ontology=$root/obo-snapshot/verified-xml/ncbitaxon.xml
prefix=$root/diagnostics/konclude-sparse-fingerprint/ncbitaxon
test "$(sha256sum "$recovery" | awk '{print $1}')" = \
  fa3fbdf1d978a81db0e8d28d40deb3150e3b2c9014b6c9c42a4e37c5bf56b6e7
test "$(sha256sum "$fingerprinter" | awk '{print $1}')" = \
  287c240260deac31d047c63893c7565cbd0a27b50c5e454bc4b82dc77fea6bb7
test "$(sha256sum "$validator" | awk '{print $1}')" = \
  5ae4d5d6ae897677bb515ef7715c13557c97f6dfbf926fae70c0af41268aa6ac
test "$(sha256sum "$runner" | awk '{print $1}')" = \
  2e198464d818ec7b8235f9e829eab5178bd5261aca5674de90cc31d54e2be3cd

prestate=$root/diagnostics/konclude-recovery-prestate
mkdir -p "$prestate"
cp "$result" "$prestate/ncbitaxon.result.fingerprint-error.json"
cp "$root/current-results/konclude/ncbitaxon.stderr" \
  "$prestate/ncbitaxon.stderr"
sha256sum "$prestate/ncbitaxon.result.fingerprint-error.json" \
  "$prestate/ncbitaxon.stderr" > "$prestate/ncbitaxon.sha256"

/usr/bin/python3 "$recovery" \
  --result "$result" --taxonomy "$taxonomy" \
  --source-ontology "$source" --runtime-ontology "$runtime_ontology" \
  --recovery-prefix "$prefix" --fingerprinter "$fingerprinter" \
  --expected-array-job-id 51028377 --fingerprint-job-id 51032807 \
  --differential-job-id 51032472
/usr/bin/python3 "$validator" --result "$result" --baseline konclude \
  --ontology-id ncbitaxon --ontology "$source" \
  --input-ontology "$runtime_ontology" --runtime "$runtime" --runner "$runner"
printf 'KONCLUDE_BIG_RECOVERY_OK\tncbitaxon\n'
