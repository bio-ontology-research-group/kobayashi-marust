#!/bin/bash
#SBATCH --job-name=konclude-kpset-debug
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=8
#SBATCH --mem=32G
#SBATCH --output=/ibex/scratch/hohndor/km/kpset_special_ref_20260711/build-konclude-debug-%j.out

set -euo pipefail
module load qt/5.15.5/gnu-12.2.0

ROOT=/ibex/scratch/hohndor/km/Konclude-debug
cd "$ROOT"
rm -rf release GeneratedFiles Release Makefile .qmake.stash
qmake -o Makefile KoncludeWithoutRedland.pro
mkdir -p Release GeneratedFiles/release release
make -j "$SLURM_CPUS_PER_TASK"
sha256sum Release/Konclude
