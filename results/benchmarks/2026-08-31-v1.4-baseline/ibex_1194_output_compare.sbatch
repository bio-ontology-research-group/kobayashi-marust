#!/bin/bash
#SBATCH --job-name=km-v14-1194-compare
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --nodes=1
#SBATCH --cpus-per-task=2
#SBATCH --mem=32G
#SBATCH --time=00:10:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v14-1194-output-compare-bottom-fix-20260901/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/v14-1194-output-compare-bottom-fix-20260901
candidate=/ibex/scratch/hohndor/km/v14-1194-existential-abox-bottom-fix-20260901/classification.json
reference=/ibex/scratch/hohndor/km/v14-1194-tbox-only-20260901/classification.json
reference_receipt=/ibex/scratch/hohndor/km/v14-1194-tbox-only-20260901/receipt.txt
candidate_receipt=/ibex/scratch/hohndor/km/v14-1194-existential-abox-bottom-fix-20260901/receipt.txt
mkdir -p "$root"
grep -Fxq 'rc=0' "$candidate_receipt"
candidate_sha=$(sha256sum "$candidate" | cut -d' ' -f1)
grep -Fxq "output_sha256=$candidate_sha" "$candidate_receipt"
grep -Fxq 'tbox_sha256=31e6c1893e143e7b356358de52e29c21336229af03bc0ae706da8a9717493903' "$reference_receipt"
grep -Fxq 'binary_sha256=cb9eabac9f5e4f351947b69f5f61df85cdf450da7f4f398b17cf34b79620aa7d' "$reference_receipt"
grep -Fxq 'classify_rc=0' "$reference_receipt"
reference_sha=$(sha256sum "$reference" | cut -d' ' -f1)

export TMPDIR=${SLURM_TMPDIR:-$root}
python3 - "$candidate" "$TMPDIR/candidate.pairs" "$root/candidate-summary.json.tmp" <<'PY'
import hashlib, json, sys
source, pairs_path, summary_path = sys.argv[1:]
with open(source, encoding="utf-8") as stream:
    value = json.load(stream)
digest = hashlib.sha256()
with open(pairs_path, "w", encoding="utf-8") as pairs:
    for pair in value["subsumptions"]:
        row = json.dumps(pair, ensure_ascii=False, separators=(",", ":"))
        digest.update(row.encode())
        digest.update(b"\n")
        pairs.write(row + "\n")
summary = {
    "consistent": value["consistent"],
    "dropped": value["dropped"],
    "unsatisfiable": value["unsatisfiable"],
    "pairs": len(value["subsumptions"]),
    "ordered_pair_sha256": digest.hexdigest(),
}
with open(summary_path, "w", encoding="utf-8") as stream:
    json.dump(summary, stream, sort_keys=True)
PY
python3 - "$reference" "$TMPDIR/reference.pairs" "$root/reference-summary.json.tmp" <<'PY'
import hashlib, json, sys
source, pairs_path, summary_path = sys.argv[1:]
with open(source, encoding="utf-8") as stream:
    value = json.load(stream)
digest = hashlib.sha256()
with open(pairs_path, "w", encoding="utf-8") as pairs:
    for pair in value["subsumptions"]:
        row = json.dumps(pair, ensure_ascii=False, separators=(",", ":"))
        digest.update(row.encode())
        digest.update(b"\n")
        pairs.write(row + "\n")
summary = {
    "consistent": value["consistent"],
    "dropped": value["dropped"],
    "unsatisfiable": value["unsatisfiable"],
    "pairs": len(value["subsumptions"]),
    "ordered_pair_sha256": digest.hexdigest(),
}
with open(summary_path, "w", encoding="utf-8") as stream:
    json.dump(summary, stream, sort_keys=True)
PY

LC_ALL=C sort -u "$TMPDIR/candidate.pairs" > "$TMPDIR/candidate.sorted"
LC_ALL=C sort -u "$TMPDIR/reference.pairs" > "$TMPDIR/reference.sorted"
candidate_only=$(LC_ALL=C comm -23 "$TMPDIR/candidate.sorted" "$TMPDIR/reference.sorted" | wc -l)
reference_only=$(LC_ALL=C comm -13 "$TMPDIR/candidate.sorted" "$TMPDIR/reference.sorted" | wc -l)
{
  echo "job=$SLURM_JOB_ID"
  echo "host=$(hostname)"
  echo "candidate_sha256=$candidate_sha"
  echo "reference_sha256=$reference_sha"
  echo "candidate_only=$candidate_only"
  echo "reference_only=$reference_only"
} > "$root/receipt.txt.tmp"
set +o pipefail
LC_ALL=C comm -3 "$TMPDIR/candidate.sorted" "$TMPDIR/reference.sorted" | head -40 \
  > "$root/first-differences.txt.tmp"
set -o pipefail
for file in candidate-summary.json reference-summary.json receipt.txt first-differences.txt; do
  mv "$root/$file.tmp" "$root/$file"
done
cat "$root/receipt.txt"
cat "$root/candidate-summary.json"
echo
cat "$root/reference-summary.json"
echo
cat "$root/first-differences.txt"
