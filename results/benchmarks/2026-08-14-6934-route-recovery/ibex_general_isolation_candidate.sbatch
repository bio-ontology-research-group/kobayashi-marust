#!/bin/bash
#SBATCH --job-name=km-6934-general-isolation
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:04:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/route-6934-v020-20260814/general-isolation-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/route-6934-v020-20260814
binary=$root/km-6934-general-isolation
expected=9b93cd0d26e43ec83eed59d8b28f45a95555978ae158d369308c8bf37bd3af4c
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_6934.owl
gold=/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__ore_ont_6934.owl.sig.gz
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]
out=$root/general-isolation-results
mkdir -p "$out" "$root/general-isolation-failures"
work=${SLURM_TMPDIR:-/tmp}/km-6934-general-isolation-$SLURM_JOB_ID
/usr/bin/python3 "$harness/full_panel_run_one.py" \
  --kind km --arm general_isolation --ontology "$ontology" --binary "$binary" \
  --workers 16 --timeout 60 --memcap-mb 20480 --gold "$gold" \
  --gold-kind konclude --workdir "$work" \
  --failures-dir "$root/general-isolation-failures" \
  --checkpoint "$out/result.checkpoint.json" --capture-km-route \
  --env KM_ROUTE=manual --env KM_MECHANISM=ht \
  --env KM_THREADS=16 --env KM_PAR_MEM_GB=18 --env KM_HT_MEM_GB=18 \
  --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_ABSORB=1 \
  --env KM_HT_FORCE=1 --env KM_HT_MODE=race \
  --env KM_HT_ONLY=general --env KM_HT_NICE=0 \
  > "$out/result.json.tmp"
mv "$out/result.json.tmp" "$out/result.json"
jq -c '{status,verdict,wall_s,peak_mb,signature_sha256,binary_sha256}' "$out/result.json"
