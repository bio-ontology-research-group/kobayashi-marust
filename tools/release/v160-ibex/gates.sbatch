#!/bin/bash
#SBATCH --job-name=km160-gates
#SBATCH --partition=batch
#SBATCH --account=pi-hohndor
#SBATCH --cpus-per-task=16
#SBATCH --mem=192G
#SBATCH --time=12:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/logs/gates-%j.log
# Five Lean gates of v1.6.0-rc1 on Ibex (tools/cert_ibex.py gates).
set -euo pipefail
module load python/3.11.0 >/dev/null 2>&1
cd /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
mkdir -p src/lean/.lake
[ -d src/lean/.lake/packages/mathlib ] || cp -a lake-packages src/lean/.lake/packages
export KM_CERT_LEAN_THREADS=4
python3 tools/cert_ibex.py /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111 gates
echo GATES-DONE
