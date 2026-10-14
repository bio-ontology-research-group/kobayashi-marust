#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=01:10:00
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-pair-audit
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/audit-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
cd "$root"
sha256sum -c audit-files.sha256
/usr/bin/python3.9 "$root/audit_pairs.py" "$1"
