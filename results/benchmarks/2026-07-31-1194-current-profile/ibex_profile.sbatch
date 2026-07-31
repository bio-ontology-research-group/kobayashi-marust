#!/bin/bash
# Profile the current default CB route for ORE 1194 without doing compute on
# the IBEX login node.  This is diagnostic evidence, not a correctness result.
#SBATCH --job-name=km-1194-prof
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/1194-current-profile-20260731/slurm-%j.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/1194-current-profile-20260731
binary=/ibex/scratch/hohndor/km/adaptive-composite-layout-v14-full-20260731/km
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
work=${SLURM_TMPDIR:-/tmp}/km-1194-profile-${SLURM_JOB_ID}
mkdir -p "$root" "$work"

sha256sum "$binary" "$ontology" | tee "$root/input-${SLURM_JOB_ID}.sha256"

/usr/bin/time -v "$binary" ofn "$ontology" --meta "$work/1194.meta.json" \
  >"$work/1194.clauses.json" 2>"$root/frontend-${SLURM_JOB_ID}.log"

# Keep one worker so the diagnostic identifies per-query saturation work rather
# than aggregate process-tree pressure from the production parallel portfolio.
# timeout sends SIGINT first so Rust can flush ordinary stderr diagnostics.
set +e
/usr/bin/time -v timeout --signal=INT --kill-after=15s 300s \
  env KM_NOMINALS=1 KM_THREADS=1 KM_PROF=1 KM_PROF_TIME=1 KM_CTXSPLIT=1 \
  "$binary" engine <"$work/1194.clauses.json" \
  >"$root/engine-${SLURM_JOB_ID}.json" 2>"$root/engine-${SLURM_JOB_ID}.log"
rc=$?
set -e

printf 'rc=%s\n' "$rc" | tee "$root/status-${SLURM_JOB_ID}.txt"
cp "$work/1194.meta.json" "$root/meta-${SLURM_JOB_ID}.json"
exit 0
