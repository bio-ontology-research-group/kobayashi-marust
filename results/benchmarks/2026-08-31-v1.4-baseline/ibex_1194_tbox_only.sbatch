#!/bin/bash
#SBATCH --job-name=km-v14-1194-tbox
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=20G
#SBATCH --time=00:07:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-tbox-only-20260901/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-1194-tbox-only-20260901
source=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
source_sha=72082c4ce0e5008589256eba0aa50957c04d294ff1e065b18cf014cc59b870e2
binary=/ibex/scratch/hohndor/km/v1.3.0-candidate-5c64a02/km
binary_sha=cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d
[[ $(sha256sum "$source" | cut -d' ' -f1) == "$source_sha" ]]
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$binary_sha" ]]
mkdir -p "$root"

# Diagnostic projection only. ORE1194's source profile proves that every ABox
# axiom is a ClassAssertion; the release may use this view only after an exact
# consistency certificate for the omitted assertions is implemented.
awk '!/^ClassAssertion\(/' "$source" > "$root/ore_ont_1194.tbox.owl.tmp"
mv "$root/ore_ont_1194.tbox.owl.tmp" "$root/ore_ont_1194.tbox.owl"
grep -q '^ClassAssertion(' "$root/ore_ont_1194.tbox.owl" && exit 90

set +e
/usr/bin/time -v -o "$root/profile.time.tmp" \
  timeout --signal=TERM --kill-after=10 60 \
  "$binary" profile "$root/ore_ont_1194.tbox.owl" \
  > "$root/profile.json.tmp" 2> "$root/profile.stderr.tmp"
profile_rc=$?
/usr/bin/time -v -o "$root/classify.time.tmp" \
  timeout --signal=TERM --kill-after=10 260 \
  env KM_ROUTE=auto KM_TIMING=1 \
  "$binary" classify "$root/ore_ont_1194.tbox.owl" \
  > "$root/classification.json.tmp" 2> "$root/classify.stderr.tmp"
classify_rc=$?
set -e

for stem in profile.time profile.json profile.stderr classify.time classification.json classify.stderr; do
  mv "$root/$stem.tmp" "$root/$stem"
done
{
  echo "job=$SLURM_JOB_ID"
  echo "host=$(hostname)"
  echo "source_sha256=$source_sha"
  echo "tbox_sha256=$(sha256sum "$root/ore_ont_1194.tbox.owl" | cut -d' ' -f1)"
  echo "binary_sha256=$binary_sha"
  echo "profile_rc=$profile_rc"
  echo "classify_rc=$classify_rc"
} > "$root/receipt.txt"

cat "$root/receipt.txt"
cat "$root/profile.json"
grep -E 'KM_TIMING|Elapsed|Maximum resident|Exit status' \
  "$root/classify.stderr" "$root/classify.time" || true
wc -c "$root/classification.json"
