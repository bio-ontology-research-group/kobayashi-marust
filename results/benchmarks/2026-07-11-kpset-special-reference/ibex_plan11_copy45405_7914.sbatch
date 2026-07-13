#!/bin/bash
#SBATCH --job-name=p11-copy45405
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:05:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --output=/home/hohndor/bench/ore_jobs/plan11-copy45405-7914-%j.out

set -u
cd "$HOME/bench"

/usr/bin/time -v \
  -o "$HOME/bench/ore_jobs/plan11-copy45405-7914.time" \
  timeout 240 env \
    KM_TRIGGER_ABSORB=1 \
    KM_KEEP_CHAIN_AXIOMS=1 \
    KM_HT_STATS=1 \
    KM_BRIDGE_PROGRESS=1 \
    KM_BRIDGE_PROBE_BUDGET_S=30 \
    KM_BRIDGE_RETRY_ROUNDS=0 \
    KM_HT_SATURATION_BUDGET_S=180 \
    KM_HT_MEM_GB=18 \
    KM_PAR_MEM_GB=18 \
    KM_THREADS=16 \
    KM_BRIDGE_ONLY_SUBJECT=9180 \
    KM_SAT_ADD_TRACE_TAG=45405 \
    km/km-or-plan11 classify \
    "$HOME/ore2015/pool_sample/files/ore_ont_7914.owl" \
  > "$HOME/bench/ore_jobs/plan11-copy45405-7914.json" \
  2> "$HOME/bench/ore_jobs/plan11-copy45405-7914.stderr"
