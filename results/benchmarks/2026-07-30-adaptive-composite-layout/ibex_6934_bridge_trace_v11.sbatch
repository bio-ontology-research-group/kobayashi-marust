#!/bin/bash
# Diagnose the exact complete-or-defer gate for ORE 6934 on the v11 binary.
# This is a read-only route trace, not a solve claim.
#SBATCH --job-name=km-v11-6934-bridge-trace
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731/6934-trace/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/adaptive-composite-layout-v11-20260731
km_root=/ibex/scratch/hohndor/km
probe=$root/6934-trace
ontology=$km_root/corpus/ore_ont_6934.owl
work=${SLURM_TMPDIR:-/tmp}/km-v11-6934-trace-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$probe" "$work"

expected=cb492d92948460671c07cb08029d188b03f0c43809efe837c70918cd4b9f08c5
observed=$(/usr/bin/sha256sum "$root/km" | /usr/bin/cut -d' ' -f1)
test "$observed" = "$expected"

set +e
timeout 240 /usr/bin/prlimit --as=21474836480 -- \
  /usr/bin/env KM_ROUTE=ht_bridge KM_BRIDGE_TRACE=1 KM_BRIDGE_TRACE2=1 \
  "$root/km" classify "$ontology" \
  > "$probe/ht_bridge.stdout.tmp" 2> "$probe/ht_bridge.stderr.tmp"
rc=$?
set -e
/usr/bin/mv "$probe/ht_bridge.stdout.tmp" "$probe/ht_bridge.stdout"
/usr/bin/mv "$probe/ht_bridge.stderr.tmp" "$probe/ht_bridge.stderr"

echo "HT_BRIDGE_TRACE_COMPLETE rc=$rc binary_sha256=$observed"
echo "stdout_bytes=$(/usr/bin/wc -c < "$probe/ht_bridge.stdout")"
echo "stderr_bytes=$(/usr/bin/wc -c < "$probe/ht_bridge.stderr")"
/usr/bin/tail -n 200 "$probe/ht_bridge.stderr"

# Bypass only the outer route gate to expose the converted TInput and the
# bridge's independent inner certificate. The resulting taxonomy is diagnostic
# and is not promoted by this job.
set +e
timeout 240 /usr/bin/prlimit --as=21474836480 -- \
  /usr/bin/env KM_ROUTE=manual KM_MECHANISM=ht KM_TRIGGER_ABSORB=1 \
  KM_HT_FORCE=1 KM_HT_MODE=race KM_HT_NICE=0 \
  KM_DUMP_TIN="$probe/6934.tinput.json" \
  KM_BRIDGE_TRACE=1 KM_BRIDGE_TRACE2=1 KM_HT_TRACE=1 \
  "$root/km" classify "$ontology" \
  > "$probe/forced_inner.stdout.tmp" 2> "$probe/forced_inner.stderr.tmp"
forced_rc=$?
set -e
/usr/bin/mv "$probe/forced_inner.stdout.tmp" "$probe/forced_inner.stdout"
/usr/bin/mv "$probe/forced_inner.stderr.tmp" "$probe/forced_inner.stderr"

echo "FORCED_INNER_TRACE_COMPLETE rc=$forced_rc"
echo "stdout_bytes=$(/usr/bin/wc -c < "$probe/forced_inner.stdout")"
echo "stderr_bytes=$(/usr/bin/wc -c < "$probe/forced_inner.stderr")"
/usr/bin/tail -n 300 "$probe/forced_inner.stderr"
