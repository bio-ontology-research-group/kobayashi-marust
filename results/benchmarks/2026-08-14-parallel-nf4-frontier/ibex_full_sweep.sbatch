#!/bin/bash
#SBATCH --job-name=km-par-nf4-full
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:12:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --array=0-591%40
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/parallel-nf4-frontier-20260814/full-sweep/slurm-%A_%a.out

set -euo pipefail
template=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/ibex_full_sweep.sbatch
generated=${SLURM_TMPDIR:-/tmp}/km-par-nf4-full-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|certified-el-typed-handoff-20260814|parallel-nf4-frontier-20260814|g' \
  -e 's|13b4d406aaddb4b94d1d9f9740cfd5839df851193d049bd76f911a3f1ab84e30|b51af8f49e59f4c74515bb2677e68706a585a2d851ae838275046a81b77fe965|g' \
  -e 's|km_route_auto_certified_el_typed|km_route_auto_parallel_nf4_frontier|g' \
  "$template" > "$generated"
/bin/bash "$generated"
