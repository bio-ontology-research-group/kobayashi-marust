#!/bin/bash
# Rebuild the production KM release binaries from the synced payg-strategy source.
# Produces target/release/{kobayashi-marust,ofn,elc,tableau_cli} = the "new"
# (clauses_cand + SmallVec, 183c3c8) engine that won the avg-performance portfolio
# (faster + lower mean RSS than the deployed baseline, +16444).
#SBATCH --job-name=km_build
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=0:40:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/kmbuild-%j.out
set -u
KM=/ibex/scratch/hohndor/km
source "$HOME/.cargo/env" 2>/dev/null || true
cd $KM/engine || exit 1
# rsync->cargo mtime gotcha: force a rebuild by touching sources.
find src -name '*.rs' -exec touch {} +
echo "=== build $(date +%T) ==="
nice cargo build --release 2>&1 | tail -6
echo "=== test $(date +%T) ==="
nice cargo test --release 2>&1 | grep -E "^test result|error\[|error:|FAILED" | head -40
echo "=== binaries ==="
ls -la --time-style=+%Y-%m-%d_%H:%M target/release/kobayashi-marust target/release/ofn target/release/elc target/release/tableau_cli
echo "=== DONE $(date +%T) ==="
