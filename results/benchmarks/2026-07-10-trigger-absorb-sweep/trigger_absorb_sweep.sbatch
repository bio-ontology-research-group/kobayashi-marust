#!/bin/bash
#SBATCH --job-name=km_trigger_sweep
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=00:25:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --output=/ibex/scratch/hohndor/km/trigger_sweep_20260710/slurm-%A_%a.out

set -u
module load python/3.11.0 2>/dev/null || true

KM=/ibex/scratch/hohndor/km
BIN=$KM/engine/target/release/km
CORPUS=$KM/corpus
GOLD=$KM/gold
SW=$KM/trigger_sweep_20260710
RESDIR=$SW/res
OUTDIR=$SW/out
mkdir -p "$RESDIR" "$OUTDIR"

mapfile -t ONTS < "$KM/fullsweep/onts.txt"
ONT=${ONTS[${SLURM_ARRAY_TASK_ID:-0}]}
[ -z "${ONT:-}" ] && exit 0
F=$CORPUS/$ONT
[ -f "$F" ] || { echo "missing $F"; exit 0; }

GSIG=$GOLD/konclude__$ONT.sig.gz
RES=$RESDIR/$ONT.jsonl
: > "$RES"

while IFS='|' read -r NAME ENVVARS; do
    [ -z "$NAME" ] && continue
    OJ=$OUTDIR/${ONT}__${NAME}.json
    TF=$OUTDIR/${ONT}__${NAME}.time
    t0=$SECONDS
    /usr/bin/time -v -o "$TF" env $ENVVARS KM_PAR_MEM_GB=18 \
        timeout 240 "$BIN" classify "$F" > "$OJ" 2>/dev/null
    rc=$?
    wall=$((SECONDS - t0))
    mem=$(grep -oE "Maximum resident set size .kbytes.: [0-9]+" "$TF" 2>/dev/null | grep -oE "[0-9]+$")

    if [ "$rc" -eq 124 ]; then
        status=timeout
    elif [ "$rc" -ne 0 ]; then
        status=error
    elif grep -q '"consistent"' "$OJ" 2>/dev/null; then
        status=ok
    else
        status=nojson
    fi

    if [ "$status" = ok ]; then
        read -r verdict extra miss < <(python3 "$KM/fullsweep/cmp_gold.py" "$OJ" "$GSIG")
    else
        verdict=$status
        extra=0
        miss=0
    fi

    solved=0
    if [ "$status" = ok ] && { [ "$verdict" = match ] || [ "$verdict" = nogold ] || [ "$verdict" = incons ]; }; then
        solved=1
    fi

    printf '{"ont":"%s","config":"%s","status":"%s","verdict":"%s","extra":%s,"miss":%s,"solved":%s,"wall_s":%s,"peak_kb":%s,"rc":%s}\n' \
        "$ONT" "$NAME" "$status" "$verdict" "${extra:-0}" "${miss:-0}" \
        "$solved" "$wall" "${mem:-0}" "$rc" >> "$RES"
    rm -f "$OJ" "$TF"
done < "$SW/configs.txt"

echo "DONE $ONT $(date +%T)"
