#!/bin/bash
# Package final current-corpus evidence after strict aggregation succeeds.
# Submit with --dependency=afterok:<final-aggregate-job>.
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=8G
#SBATCH --job-name=km-paper-current-package-v2
#SBATCH --output=/ibex/scratch/hohndor/km/paper-benchmark-20260830/logs/current-package-v2-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/paper-benchmark-20260830
out=$root/archive-v2
readme=$root/runner-tools/current-evidence-README.md
cd "$root"
mkdir -p "$out/staging"
test -s "$readme"
(cd "$root/final-v2" && sha256sum -c SHA256SUMS)
test "$(find "$root/current-results" -mindepth 2 -maxdepth 2 -type f \
  -name '*.result.json' | wc -l)" -eq 1512

cp "$readme" "$out/staging/README.md"
files=$out/staging/FILELIST.txt
{
  printf '%s\n' archive-v2/staging/README.md
  find final-v2 -maxdepth 1 -type f
  find current-results -mindepth 2 -maxdepth 2 -type f \
    \( -name '*.result.json' -o -name '*.fingerprint.json' \
       -o -name '*.fingerprint.nodes.tsv.gz' \
       -o -name '*.fingerprint.unsat.txt.gz' -o -name '*.stderr' \
       -o -name '*.time' \)
  find obo-snapshot -type f \
    \( -path '*/import-receipts/*' -o -path '*/profiles/*' \
       -o -path '*/rdfxml-receipts/*' \
       -o -path '*/verified-xml-receipts/*' \
       -name 'obo-freeze-20260830.tsv' -o -name 'registry-freeze.json' \)
  find diagnostics -type f ! -name '*.taxonomy.*'
  find runner-tools -maxdepth 2 -type f \
    \( -name '*.py' -o -name '*.java' -o -name '*.sbatch' \
       -o -name '*.tsv' -o -name '*.json' -o -name '*.md' \)
  find logs -maxdepth 1 -type f \
    \( -name 'java-full-*' -o -name 'java-revalidate-*' \
       -o -name 'current-final-*' -o -name 'native-full-*' \
       -o -name 'jfact-diff-*' -o -name 'jfact-unsat-*' \
       -o -name 'kisao-unsat-*' -o -name 'entailment-explanation-*' \
       -o -name '*fingerprint*' \)
  for name in baselines.tsv.final execution-jobs.tsv.final \
      preparation-artifacts.tsv.final; do test -s "$name"; printf '%s\n' "$name"; done
} | LC_ALL=C sort -u > "$files"

if grep -E '(^|/)(merged|sources|runtimes)/|\.taxonomy\.|\.jar$|Konclude-build' "$files"; then
  echo 'forbidden payload entered evidence file list' >&2
  exit 1
fi
test "$(grep -Ec '^current-results/[^/]+/[^/]+\.result\.json$' "$files")" -eq 1512

tar_path=$out/current-obo-evidence-20260830.tar
gzip_path=$tar_path.gz
(cd "$root" && tar --format=posix --sort=name \
  --mtime='2026-08-30 00:00:00 UTC' --owner=0 --group=0 --numeric-owner \
  --transform='s#^final-v2/#final/#' \
  --transform='s#^archive-v2/#archive/#' \
  --no-recursion -cf "$tar_path" -T "$files")
gzip -n -f "$tar_path"
sha256sum "$gzip_path" > "$out/current-obo-evidence-20260830.tar.gz.sha256"
printf 'CURRENT_EVIDENCE_PACKAGE_V2_OK\t%s\n' "$(stat -c %s "$gzip_path")"
