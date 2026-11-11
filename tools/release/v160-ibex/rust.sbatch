#!/bin/bash
#SBATCH --job-name=km160-rust
#SBATCH --partition=batch
#SBATCH --account=pi-hohndor
#SBATCH --cpus-per-task=8
#SBATCH --mem=96G
#SBATCH --time=16:00:00
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111/logs/rust-%j.log
# Full Rust suite of v1.6.0-rc1 on Ibex (tools/cert_ibex.py rust); refuses unless all five gates passed.
set -euo pipefail
module load python/3.11.0 >/dev/null 2>&1
cd /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111
python3 tools/cert_ibex.py /ibex/scratch/projects/c2014/hohndor/km/v160-release-20261111 rust
echo RUST-DONE
