#!/bin/bash
# Long, high-memory reference closure for ORE 1194. This is not the 240 s
# production benchmark; it establishes whether the guarded candidate reaches a
# complete certified model and captures the resulting taxonomy for comparison.
#SBATCH --job-name=km1194-ref
#SBATCH --account=pi-hohndor
#SBATCH --partition=largemem
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=1
#SBATCH --mem=120G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/1194-long-reference/slurm-%j.out

set -u

ROOT=/ibex/scratch/hohndor/km/routing_20260715/1194-long-reference
BIN="$ROOT/elc-combined"
INPUT="$ROOT/1194.clauses.json"
TAG=combined-small-virtual-bulk-cover
OUT="$ROOT/$TAG.out.json"
TMP="$OUT.tmp.$SLURM_JOB_ID"
ERR="$ROOT/$TAG.err"
TIME="$ROOT/$TAG.time"
DONE="$ROOT/$TAG.complete.json"

mkdir -p "$ROOT"
bin_sha=$(sha256sum "$BIN" | awk '{print $1}')
input_sha=$(sha256sum "$INPUT" | awk '{print $1}')

if [[ -s "$DONE" && -s "$OUT" ]] && python3 - "$DONE" "$bin_sha" "$input_sha" <<'PY'
import json, sys
p, binary, source = sys.argv[1:]
x = json.load(open(p))
raise SystemExit(0 if x.get("status") == "ok" and x.get("binary_sha256") == binary and x.get("input_sha256") == source else 1)
PY
then
    echo "checkpoint already complete: $DONE"
    exit 0
fi

rm -f "$TMP" "$DONE"
printf 'job_id=%s\nhost=%s\nbinary_sha256=%s\ninput_sha256=%s\nstarted=%s\n' \
    "$SLURM_JOB_ID" "$(hostname)" "$bin_sha" "$input_sha" "$(date -Is)" > "$ROOT/$TAG.running"

/usr/bin/time -v -o "$TIME" \
    timeout --signal=INT --kill-after=30s 10800 \
    env KM_ELC_CERT=2 KM_ELC_DEBUG=1 KM_ELC_TIMING=1 \
    "$BIN" < "$INPUT" > "$TMP" 2> "$ERR"
rc=$?

status=failed
if [[ $rc -eq 0 && -s "$TMP" ]] && python3 - "$TMP" <<'PY'
import json, sys
x = json.load(open(sys.argv[1]))
assert isinstance(x, dict) and x
PY
then
    mv "$TMP" "$OUT"
    status=ok
fi

python3 - "$DONE" "$status" "$rc" "$bin_sha" "$input_sha" "$OUT" <<'PY'
import json, os, sys
p, status, rc, binary, source, out = sys.argv[1:]
tmp = p + ".tmp"
with open(tmp, "w") as fh:
    json.dump({
        "status": status,
        "rc": int(rc),
        "binary_sha256": binary,
        "input_sha256": source,
        "output": out,
        "output_bytes": os.path.getsize(out) if os.path.exists(out) else 0,
    }, fh, sort_keys=True)
    fh.write("\n")
os.replace(tmp, p)
PY
rm -f "$ROOT/$TAG.running"

[[ "$status" == ok ]]
