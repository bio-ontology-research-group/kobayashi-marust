#!/bin/bash
# Keep the reasoner in a child Slurm step whose hard memory cgroup cannot kill
# the parent Python supervisor.  The watchdog still enforces the benchmark's
# 20 GiB measured-tree cap; 24 GiB is only containment headroom for a parallel
# allocation burst between watchdog samples.
set -euo pipefail

root=/ibex/scratch/hohndor/km/integrated-main-full-20260730
exec /usr/bin/srun \
  --overlap \
  --exact \
  --ntasks=1 \
  --cpus-per-task="${SLURM_CPUS_PER_TASK:-16}" \
  --mem=24G \
  --kill-on-bad-exit=1 \
  "$root/km" "$@"
