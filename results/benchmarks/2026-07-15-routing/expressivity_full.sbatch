#!/bin/bash
# Official Konclude structure-summary codes for all 592 ORE inputs. The helper
# stops immediately after the post-preprocessing expressivity log line.
#SBATCH --job-name=kon-expr-all
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=2
#SBATCH --mem=22G
#SBATCH --array=0-591%48
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/expr-%A_%a.out

set -euo pipefail

root=/ibex/scratch/hohndor/km/routing_20260715
km_root=/ibex/scratch/hohndor/km
mapfile -t ontologies < "$root/onts.txt"
ontology=${ontologies[${SLURM_ARRAY_TASK_ID:-0}]}
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
mkdir -p "$root/konclude-expressivity"
/usr/bin/python3 "$root/konclude_expr_one.py" \
  --binary "$km_root/Konclude-official" --ontology "$local_ontology" \
  --timeout 240 --memcap-mb 20480 \
  > "$root/konclude-expressivity/$ontology.json"
/usr/bin/rm -f "$local_ontology"
