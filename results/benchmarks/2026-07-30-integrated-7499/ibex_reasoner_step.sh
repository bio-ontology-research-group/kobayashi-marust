#!/bin/bash
# Keep the reasoner in a child Slurm step whose hard memory cgroup cannot kill
# the parent Python supervisor.  The watchdog still enforces the benchmark's
# 20 GiB measured-tree cap; 24 GiB is only containment headroom for a parallel
# allocation burst between watchdog samples.
set -euo pipefail

root=/ibex/scratch/hohndor/km/integrated-main-full-20260730
set +e
/opt/slurm/cluster/ibex/install-v2/RedHat-9/bin/srun \
  --overlap \
  --exact \
  --ntasks=1 \
  --cpus-per-task="${SLURM_CPUS_PER_TASK:-16}" \
  --mem=24G \
  --kill-on-bad-exit=1 \
  /usr/bin/timeout --signal=KILL 238 \
  "$root/km" "$@"
rc=$?
set -e

# End the nested step before the parent runner's 240-second hard alarm. GNU
# timeout returns 137 when its KILL signal was needed; normalize either timeout
# code and leave a machine-readable marker for the benchmark runner.
if [[ $rc -eq 124 || $rc -eq 137 ]]; then
  echo "KM_NESTED_TIMEOUT" >&2
  exit 124
fi
exit "$rc"
