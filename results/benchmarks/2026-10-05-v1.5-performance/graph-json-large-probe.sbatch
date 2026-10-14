#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclude=cn603-25-l
#SBATCH --cpus-per-task=1
#SBATCH --mem=24G
#SBATCH --time=00:35:00
#SBATCH --array=0-5%3
#SBATCH --export=NONE
#SBATCH --job-name=km-v150-graph-json-large-probe
#SBATCH --output=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/graph-json-large-probe-%A_%a.log
set -euo pipefail
root=/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005
export TMPDIR="$root/graph-json-large-probe-tmp-${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}"
mkdir -p "$TMPDIR"
cd "$root"
sha256sum -c runner-files.sha256
sha256sum -c graph-json-large-probe-files.sha256
/usr/bin/python3.9 "$root/probe_graph_json_large.py"
