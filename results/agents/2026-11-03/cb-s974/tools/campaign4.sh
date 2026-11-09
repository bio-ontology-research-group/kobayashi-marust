#!/bin/bash
# campaign4.sh FINAL_BIN BASE_BIN : the validation of the final binary (v7):
# the two seeds 20 times on both routes, the families once (automatic route
# and the cheap failed route), the 112 nominal and 16 held-out inputs, the C1
# sample, the pools (base rerun only where the final binary is not ok and the
# earlier base rerun has no row), then the test suites.
T=$(dirname $(readlink -f $0)); NEW=$1; BASE=$2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/cb-s974
P=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-self/pool
export TMPDIR=$S/tmp
mkdir -p $S/final; : > $S/final/seeds20.tsv
for i in $(seq 1 20); do
  python3 -I $T/fam_run.py $NEW $P/gold $S/final/seeds20.tsv auto,cb_plain1 1 $P/seeds/s974.ofn
  python3 -I $T/fam_run.py $NEW $P/gold $S/final/seeds20.tsv auto,seq 1 $P/seeds/s1966.ofn
done; echo "=== seeds $(date)"
: > $S/final/merge.tsv; : > $S/final/vacuous.tsv
FAM_FORCED_TIMEOUT=5 python3 -I $T/fam_run.py $NEW $S/fam-merge/gold $S/final/merge.tsv auto 1 $(ls $S/fam-merge/seeds/*.ofn | sort -V)
python3 -I $T/fam_run.py $NEW $S/fam-vacuous/gold $S/final/vacuous.tsv auto,seq 1 $(ls $S/fam-vacuous/seeds/*.ofn | sort -V)
echo "=== families $(date)"
O=$S/ore; rm -f $O/times-final.tsv
$T/ore_time.sh $NEW $T/ore-design-nominal.txt $O final KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1
python3 -I $T/ore_pair.py $O before final > $O/pair-final.txt
echo "guard fired (final): $(grep -l 'coverage guard fired' $O/out-final/*.errtail | wc -l)" >> $O/pair-final.txt
echo "=== nominal $(date)"
$T/heldout.sh $NEW final; echo "=== heldout $(date)"
mv $S/c1 $S/c1-v6; $T/c1_run.sh $BASE $NEW; echo "=== c1 $(date)"
mv $S/pools/after $S/pools/after-v5; $T/pools.sh $NEW after; echo "=== pools $(date)"
$T/tests.sh $S/tests; echo "=== tests $(date)"
