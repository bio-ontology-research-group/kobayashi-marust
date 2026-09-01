#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-ncbitaxon-fingerprint-recovery
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/km-ncbitaxon-recovery-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
recovery=$root/runner-tools/recover_km_fingerprint.py
fingerprinter=$root/runner-tools/fingerprint_km_json_sparse.py
validator=$root/runner-tools/validate_result.py.next
test "$(sha256sum "$recovery" | awk '{print $1}')" = \
  9dab442b92619a4612481162a6af744b1a4cc2b808a02be096b9eaf7cdadf548
test "$(sha256sum "$fingerprinter" | awk '{print $1}')" = \
  337411472cc53677ee8e73b54335ac404c66e6043d74d3329d1688bdb3f550b6
test "$(sha256sum "$validator" | awk '{print $1}')" = \
  5ae4d5d6ae897677bb515ef7715c13557c97f6dfbf926fae70c0af41268aa6ac
/usr/bin/python3 "$recovery" \
  --result "$root/current-results/km/ncbitaxon.result.json" \
  --taxonomy "$root/current-results/km/ncbitaxon.taxonomy.json" \
  --source-ontology "$root/obo-snapshot/merged/ncbitaxon.ofn" \
  --recovery-prefix "$root/diagnostics/km-sparse-fingerprint/ncbitaxon" \
  --fingerprinter "$fingerprinter" --expected-array-job-id 51028377 \
  --fingerprint-job-id 51031093 --differential-job-id 51030723
/usr/bin/python3 "$validator" \
  --result "$root/current-results/km/ncbitaxon.result.json" \
  --baseline km --ontology-id ncbitaxon \
  --ontology "$root/obo-snapshot/merged/ncbitaxon.ofn" \
  --runtime /ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km \
  --runner "$root/runner-tools/run_native_one.py"
printf 'KMBIG_RECOVERY_OK\tncbitaxon\n'
