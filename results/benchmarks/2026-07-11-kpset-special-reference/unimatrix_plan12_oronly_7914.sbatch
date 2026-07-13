#!/bin/bash
#SBATCH --job-name=p12-oronly-7914
#SBATCH --partition=debug
#SBATCH --time=00:08:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --exclusive
#SBATCH --exclude=unimatrix,node001
#SBATCH --output=/home/hohndor/bench/ore_jobs/plan12-oronly-7914-%j.out

set -u

variant=${1:-subject9180}
root="$HOME/bench"
binary="$root/km/km-or-plan12"
input="$HOME/ore2015/pool_sample/files/ore_ont_7914.owl"
gold="$root/ore_out/konclude__ore_ont_7914.owl.sig.gz"
prefix="$root/ore_jobs/plan12-${variant}-7914-${SLURM_JOB_ID}"
extra=()
if [[ "$variant" == "subject9180" ]]; then
  extra+=(KM_BRIDGE_ONLY_SUBJECT=9180)
  extra+=(KM_SAT_CACHE_TRACE_TAG=1440,45405,45406)
fi

sha256=$(/usr/bin/sha256sum "$binary" | /usr/bin/cut -d' ' -f1)
echo "BEGIN variant=$variant host=$(hostname) date=$(date -Is) sha256=$sha256"

/usr/bin/time -v -o "$prefix.time" \
  /usr/bin/timeout 300 /usr/bin/env \
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
    "${extra[@]}" \
    "$binary" classify "$input" \
    >"$prefix.json" 2>"$prefix.stderr"
rc=$?

status=error
comparison='{}'
signature='{}'
if [[ "$rc" -eq 124 ]]; then
  status=timeout
elif [[ "$rc" -eq 0 ]] && /usr/bin/grep -q '"consistent"' "$prefix.json"; then
  status=ok
  signature=$(/usr/bin/python3 "$root/ore_harness/json_to_sig.py" \
    "$prefix.json" "$prefix.sig.gz")
  comparison=$(/usr/bin/python3 "$root/ore_harness/sig_cmp.py" \
    "$prefix.sig.gz" "$gold")
fi

peak_kb=$(/usr/bin/grep -oE 'Maximum resident set size .kbytes.: [0-9]+' \
  "$prefix.time" 2>/dev/null | /usr/bin/grep -oE '[0-9]+$')
elapsed=$(/usr/bin/grep -oE 'Elapsed .wall clock. time .*: .*' \
  "$prefix.time" 2>/dev/null | /usr/bin/sed 's/^.*): //')
/usr/bin/python3 - "$variant" "$status" "$rc" "${peak_kb:-0}" "$elapsed" \
  "$sha256" "$signature" "$comparison" <<'PY'
import json
import sys

variant, status, rc, peak_kb, elapsed, sha256, signature, comparison = sys.argv[1:]
print(json.dumps({
    "ontology": 7914,
    "variant": variant,
    "status": status,
    "rc": int(rc),
    "peak_kb": int(peak_kb),
    "elapsed": elapsed,
    "binary_sha256": sha256,
    "signature": json.loads(signature),
    "comparison": json.loads(comparison),
}))
PY

echo "STDERR-TAIL"
/usr/bin/tail -40 "$prefix.stderr"
