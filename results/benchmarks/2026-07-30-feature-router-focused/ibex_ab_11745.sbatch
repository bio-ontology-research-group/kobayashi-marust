#!/bin/bash
# Controlled same-node A/B for the cached completion-gate patch after the
# family panel observed a non-gold 11745 result. Both binaries classify the
# same copied ontology under the same environment and resource contract.
#SBATCH --job-name=km-ab-11745
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:30:00
#SBATCH --cpus-per-task=32
#SBATCH --mem=64G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/cycle9-3215-src/slurm-%x-%j.out

set -u

root=/ibex/scratch/hohndor/km/cycle9-3215-src
frozen=/ibex/scratch/hohndor/km/feature-router-full-exclusive-20260730/km
patched=$root/km-cycle9
ont=/ibex/scratch/hohndor/km/corpus/ore_ont_11745.owl
gold=/ibex/scratch/hohndor/km/gold/konclude__ore_ont_11745.owl.sig.gz
score=$root/kmsig.py
out=$root/ab-11745-$SLURM_JOB_ID
mkdir -p "$out"

sha256sum "$frozen" "$patched" "$ont" "$gold" "$score"

for arm in frozen patched patched_repeat; do
    case "$arm" in
        frozen) bin=$frozen ;;
        *) bin=$patched ;;
    esac
    set +e
    env KM_ROUTE=auto KM_THREADS=16 \
        /usr/bin/time -q -f 'WALL=%e PEAK_KB=%M TIME_RC=%x' \
        -o "$out/$arm.time" \
        timeout 240 "$bin" classify "$ont" \
        > "$out/$arm.json" 2> "$out/$arm.err"
    rc=$?
    set -e
    echo "ARM=$arm RC=$rc $(tr '\n' ' ' < "$out/$arm.time")"
    if [ "$rc" -eq 0 ]; then
        set +e
        /usr/bin/python3 "$score" "$out/$arm.json" "$gold"
        score_rc=$?
        set -e
        echo "ARM=$arm SCORE_RC=$score_rc"
    fi
done

sha256sum "$out"/*.json "$out"/*.err "$out"/*.time
echo "AB_11745_COMPLETE job=$SLURM_JOB_ID"
