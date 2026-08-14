#!/bin/bash
#SBATCH --job-name=km-iri-bulk-full
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
#SBATCH --output=/ibex/scratch/hohndor/km/declaration-seed-20260814/full-sweep/slurm-%A_%a.out

set -euo pipefail
template=/ibex/scratch/hohndor/km/certified-el-typed-handoff-20260814/ibex_full_sweep.sbatch
generated=${SLURM_TMPDIR:-/tmp}/km-iri-bulk-full-${SLURM_JOB_ID}.sh
/usr/bin/sed \
  -e 's|certified-el-typed-handoff-20260814|declaration-seed-20260814|g' \
  -e 's|13b4d406aaddb4b94d1d9f9740cfd5839df851193d049bd76f911a3f1ab84e30|7c090417f169d5ee60992f5203e2fe62aee4e8244b50e1aadf7a03b08bf1a71a|g' \
  -e 's|km_route_auto_certified_el_typed|km_route_auto_bulk_iri_map|g' \
  "$template" > "$generated"
/bin/bash "$generated"
