#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-paper-current-final-v2
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/current-final-v2-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
aggregate=$root/runner-tools/aggregate_current.py.final-v2
render=$root/runner-tools/render_current_tables.py.final-v2

test "$(sha256sum "$aggregate" | awk '{print $1}')" = \
  5221a8cb7893f199e02d33ead643097e60bc463a78a04cda3c06e7415ac3037c
test "$(sha256sum "$render" | awk '{print $1}')" = \
  3b4b04b9d4165f5a54cbcd66c759eadb9da81b66a0fbd25f2461bca38f793849
test "$(sha256sum "$root/baselines.tsv.final" | awk '{print $1}')" = \
  de320102e150d966f57e9852c570cd15cbe8d6060ff0f4a81145d22290523b5f
test "$(sha256sum "$root/execution-jobs.tsv.final" | awk '{print $1}')" = \
  2e0dde41079ba1380126aa393470f0cfe8a166a226ff5501744e3a0e934845ef
test "$(sha256sum "$root/preparation-artifacts.tsv.final" | awk '{print $1}')" = \
  34d32bcf045d48628731a395bf80cbead7e87fa20015982633250fd04180c5b1

out=$root/final-v2
mkdir -p "$out"
/usr/bin/python3 "$aggregate" \
  --manifest "$root/obo-snapshot/obo-freeze-20260830.tsv" \
  --baselines "$root/baselines.tsv.final" \
  --execution-jobs "$root/execution-jobs.tsv.final" \
  --preparation-artifacts "$root/preparation-artifacts.tsv.final" \
  --receipts "$root/obo-snapshot/import-receipts" \
  --serialization-receipts "$root/obo-snapshot/verified-xml-receipts" \
  --profiles "$root/obo-snapshot/profiles" \
  --results "$root/current-results" \
  --output-json "$out/current-aggregate.json" \
  --disagreements-tsv "$out/current-disagreements.tsv"

/usr/bin/python3 "$render" \
  --aggregate "$out/current-aggregate.json" \
  --output "$out/current-results.tex"

test "$(/usr/bin/find "$root/current-results" -mindepth 2 -maxdepth 2 \
  -type f -name '*.result.json' | /usr/bin/wc -l)" -eq 1512
(
  cd "$root"
  /usr/bin/find current-results -mindepth 2 -maxdepth 2 -type f \
    -name '*.result.json' -print0 | /usr/bin/sort -z | /usr/bin/xargs -0 sha256sum
) > "$out/result-records.sha256"
test "$(/usr/bin/wc -l < "$out/result-records.sha256")" -eq 1512
(
  cd "$out"
  sha256sum current-aggregate.json current-disagreements.tsv current-results.tex \
    result-records.sha256
) > "$out/SHA256SUMS"
printf 'CURRENT_FINAL_V2_OK\t1512\n'
