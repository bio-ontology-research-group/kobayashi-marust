#!/bin/bash
#SBATCH --job-name=km160-pgo
#SBATCH --partition=batch
#SBATCH --account=pi-hohndor
#SBATCH --cpus-per-task=16
#SBATCH --mem=96G
#SBATCH --time=08:00:00
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/logs/pgo-%j.log
# PGO build of v1.6.0-rc1 on Ibex with the v1.5.5 recipe (tools/pgo_build_ibex.py:
# pgo_build.py with ws paths replaced by staged copies). Native glibc 2.34, so
# the GLIBC <= 2.34 audit holds by construction; the cc wrapper stays as recorded.
set -euo pipefail
module load python/3.11.0
export KM_IBEX_ROOT=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
CPUS=$(python3 -c "import os; print(','.join(map(str,sorted(os.sched_getaffinity(0)))))")
TRAIN=$(python3 -c "import os; c=sorted(os.sched_getaffinity(0)); print(','.join(map(str,c[:4])))")
echo "node $(hostname) cpus $CPUS train $TRAIN"
cd /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
python3 tools/pgo_build_ibex.py --worktree /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/src --root /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/pgo --version 1.6.0 --cpus "$CPUS" --train-cpus "$TRAIN" --jobs 16
python3 tools/pgo_build_ibex.py --worktree /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/src --root /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/pgo --clean
sha256sum pgo/km-v1.6.0-rc-pgo
objdump -T pgo/km-v1.6.0-rc-pgo | grep -o 'GLIBC_[0-9.]*' | sort -uV | tail -1
echo PGO-DONE
