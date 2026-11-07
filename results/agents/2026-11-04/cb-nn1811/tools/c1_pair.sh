#!/bin/bash
# c1_pair.sh BASE_BIN NEW_BIN : the 300-input sample of the C1 regression pool
# (c1-sample-300.txt: ORE numbers drawn with random.Random(1811) from the admitted rows of
# .work/v152-correctness-1920/full-candidate-inputs-ws.json), base and new side by side
# (two KM processes at a time, release flags, 60 s cap), compared with the pinned references.
T=$(dirname $(readlink -f $0)); BASE=$1; NEW=$2
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
O=$R/.work/agent-scratch/cb-nn1811/c1; mkdir -p $O/out
CMP=$R/.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/tools/compare_ref.py
export TMPDIR=$R/.work/agent-scratch/cb-nn1811/tmp
: > $O/summary.tsv
run() { n=$1; bin=$2; L=$3; ont="ore_ont_$n"; path="$R/v150-corpus/files/$ont.owl"
  s=$(date +%s.%N)
  env $(env | grep -o '^KM_[A-Z_]*' | sed 's/^/-u /') KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1 \
    timeout -k 5 60 $bin classify $path > $O/out/$ont.$L.json 2> $O/out/$ont.$L.err; rc=$?
  w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-7)
  agree=""; [ $rc = 0 ] && agree=$(python3 -I $CMP $ont $O/out/$ont.$L.json $O/cmp-$ont-$L 2>&1 | grep -oE '"reference": "[a-z]+", "status": "[a-z_]+"' | sed 's/"reference": //; s/, "status": /=/; s/"//g' | tr '\n' ' ')
  rm -rf $O/cmp-$ont-$L; tail -c 3000 $O/out/$ont.$L.err > $O/out/$ont.$L.errtail; rm -f $O/out/$ont.$L.err $O/out/$ont.$L.json
  echo -e "$ont\t$L\trc=$rc\twall=$w\t$agree" >> $O/summary.tsv
}
while read -r n; do
  [ -z "$n" ] && continue
  run $n $BASE base & run $n $NEW new & wait
done < $T/c1-sample-300.txt
echo DONE >> $O/summary.tsv
cp $O/summary.tsv $T/../data/c1-sample-300-summary.tsv
