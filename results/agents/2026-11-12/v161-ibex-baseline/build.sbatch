#!/bin/bash
#SBATCH --job-name=km-v161-refbuild
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=8
#SBATCH --mem=64G
#SBATCH --time=02:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v161-diag-20261112/logs/build-%j.log
# Build km-el-reference from a copy of the v1.6.0 tag tree (the certified tree stays untouched).
set -euo pipefail
I=/ibex/scratch/projects/c2014/hohndor/km/v161-diag-20261112
S=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
rm -rf $I/src-tag; cp -a $S/src $I/src-tag
cd $I/src-tag; git rev-parse HEAD; git status --porcelain --untracked-files=no | head
export PATH=$S/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:/usr/local/bin:/usr/bin:/bin
unset PYTHONPATH LD_LIBRARY_PATH
cd lean; LEAN_NUM_THREADS=8 lake build km-el-reference
cp .lake/build/bin/km-el-reference $I/km-el-reference
sha256sum $I/km-el-reference
echo BUILD-DONE
