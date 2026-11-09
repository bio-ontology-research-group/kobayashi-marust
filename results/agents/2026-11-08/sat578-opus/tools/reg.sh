#!/bin/bash
# reg.sh BIN OUT.tsv RUNS [LIST]: every row of a regression list (pool, seed, route)
# through diff_run.py on its own route, RUNS times, release flags, 60 s cap.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
BIN=$1; OUT=$2; RUNS=$3; LIST=${4:-$S/regressions-of-fbd1932c.txt}
export TMPDIR=$S/tmp DIFF_THREADS=${DIFF_THREADS:-1} DIFF_KM_TIMEOUT=60
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1${REG_EXTRA:+,$REG_EXTRA}
gold() { case $1 in
  bridge-nn-rule-fam) echo $A/bridge-nn-rule/fam/gold;;
  bridge-reflexive-fam) echo $A/bridge-reflexive/fam/gold;;
  bridge-satcache-fam) echo $A/bridge-satcache/famgold;;
  bridge-self-pools-*) echo $A/bridge-self/pools/${1#bridge-self-pools-}/gold;;
  *) echo UNKNOWN;; esac; }
for run in $(seq 1 $RUNS); do
  grep -v '^#' $LIST | while IFS=$'\t' read pool path route rest; do
    python3 -I $S/tools/diff_run.py $BIN /nonexistent $(gold $pool) $OUT $route $path
  done
done
cut -f2,3 $OUT | sort | uniq -c
