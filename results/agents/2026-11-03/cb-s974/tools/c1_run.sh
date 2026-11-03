#!/bin/bash
# c1_run.sh BASE_BIN NEW_BIN : the C1 sample (c1_sample.py), base and new
# run side by side (two KM processes), release flags, 120 s cap, each answer
# compared with the pinned references (compare_ref.py of
# results/agents/2026-11-01/bridge-defers). Rows: ontology, label, rc, wall,
# reference verdicts.
T=$(dirname $(readlink -f $0)); BASE=$1; NEW=$2
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
O=$R/.work/agent-scratch/cb-s974/c1; mkdir -p $O/out
CMP=$R/.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/tools/compare_ref.py
export TMPDIR=$R/.work/agent-scratch/cb-s974/tmp
python3 -I $T/c1_sample.py > $O/sample.tsv
: > $O/summary.tsv
run() { ont=$1; path=$2; bin=$3; L=$4
  s=$(date +%s.%N)
  env $(env | grep -o '^KM_[A-Z_]*' | sed 's/^/-u /') KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 KM_TIMING=1 \
    timeout -k 5 120 $bin classify $path > $O/out/$ont.$L.json 2> $O/out/$ont.$L.err; rc=$?
  w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-7)
  agree=""; [ $rc = 0 ] && agree=$(python3 -I $CMP $ont $O/out/$ont.$L.json $O/cmp-$ont-$L 2>&1 | grep -oE '"reference": "[a-z]+", "status": "[a-z_]+"' | sed 's/"reference": //; s/, "status": /=/; s/"//g' | tr '\n' ' ')
  rm -rf $O/cmp-$ont-$L; tail -c 3000 $O/out/$ont.$L.err > $O/out/$ont.$L.errtail; rm -f $O/out/$ont.$L.err
  gzip -f $O/out/$ont.$L.json
  echo -e "$ont\t$L\trc=$rc\twall=$w\t$agree" >> $O/summary.tsv
}
while IFS=$'\t' read -r ont path; do
  run $ont $path $BASE base & run $ont $path $NEW new & wait
done < $O/sample.tsv
echo DONE >> $O/summary.tsv
