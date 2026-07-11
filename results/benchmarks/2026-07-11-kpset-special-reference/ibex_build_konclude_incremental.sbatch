#!/bin/bash
#SBATCH --job-name=konclude-kpset-inc
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/build-konclude-inc-%j.out

set -euo pipefail
module load qt/5.15.5/gnu-12.2.0

ROOT=/ibex/scratch/hohndor/km/Konclude-debug
cd "$ROOT"
make -j "$SLURM_CPUS_PER_TASK"
sha256sum Release/Konclude
