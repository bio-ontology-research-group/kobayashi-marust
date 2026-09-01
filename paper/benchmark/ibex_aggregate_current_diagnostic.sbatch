#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-paper-current-diagnostic
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/current-diagnostic-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
script=$root/runner-tools/aggregate_current.py.next
test "$(sha256sum "$script" | awk '{print $1}')" = \
  55dcbe1ebad722d2f50b00926f87ac1a506c209292a446d5ff50c3346ce43040
/usr/bin/python3 "$script" \
  --manifest "$root/obo-snapshot/obo-freeze-20260830.tsv" \
  --baselines "$root/baselines.tsv.next" \
  --execution-jobs "$root/execution-jobs.tsv.next" \
  --preparation-artifacts "$root/preparation-artifacts.tsv.next" \
  --receipts "$root/obo-snapshot/import-receipts" \
  --serialization-receipts "$root/obo-snapshot/verified-xml-receipts" \
  --profiles "$root/obo-snapshot/profiles" \
  --results "$root/current-results" \
  --output-json "$root/diagnostics/current-live-aggregate.json" \
  --disagreements-tsv "$root/diagnostics/current-live-disagreements.tsv" \
  --allow-incomplete
printf 'CURRENT_DIAGNOSTIC_OK\n'
