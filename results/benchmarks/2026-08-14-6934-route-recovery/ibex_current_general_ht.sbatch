#!/bin/bash
#SBATCH --job-name=km-6934-current-general-ht
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/route-6934-v020-20260814/current-general-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/route-6934-v020-20260814
binary=/ibex/scratch/hohndor/km/declaration-seed-20260814/km
expected=7c090417f169d5ee60992f5203e2fe62aee4e8244b50e1aadf7a03b08bf1a71a
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
mkdir -p "$root/current-general-results" "$root/current-general-failures"
work=${SLURM_TMPDIR:-/tmp}/km-6934-current-general-$SLURM_JOB_ID
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm current_general_ht --ontology "$ontology" \
  --binary "$binary" --workers 16 --timeout 60 --memcap-mb 20480 \
  --gold "$gold" --gold-kind konclude --workdir "$work" \
  --failures-dir "$root/current-general-failures" \
  --checkpoint "$root/current-general-results/result.checkpoint.json" \
  --capture-km-route \
  --env KM_ROUTE=manual --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 \
  --env KM_HT_MEM_GB=18 --env KM_KEEP_CHAIN_AXIOMS=1 \
  --env KM_ABSORB=1 --env KM_HT_FORCE=1 --env KM_HT_MODE=race \
  --env KM_HT_ONLY=general --env KM_HT_NICE=0 \
  > "$root/current-general-results/result.json.tmp"
mv "$root/current-general-results/result.json.tmp" \
  "$root/current-general-results/result.json"
jq -c '{status,verdict,wall_s,peak_mb,signature_sha256,selected_route_trace,binary_sha256}' \
  "$root/current-general-results/result.json"
