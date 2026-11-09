#!/bin/bash
# rows.sh BIN LIST OUT.tsv [CAP]: run diff_run.py on the rows (pool, seed, route)
# of LIST, grouped by pool and route, DIFF_THREADS (default 2) at a time,
# release flags, CAP seconds (default 60). Gold is looked up per pool.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
BIN=$1; LIST=$2; OUT=$3; CAP=${4:-60}
export TMPDIR=$S/tmp DIFF_THREADS=${DIFF_THREADS:-2} DIFF_KM_TIMEOUT=$CAP
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1${ROWS_EXTRA:+,$ROWS_EXTRA}
NNR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-bridge-nn-rule/results/agents/2026-11-04/bridge-nn-rule/data/reductions
gold() { case $1 in
  sat578-fam) echo $A/sat578/famgold;;
  bridge-satcache-fam) echo $A/bridge-satcache/famgold;;
  bridge-nn-rule-fam) echo $A/bridge-nn-rule/fam/gold;;
  bridge-self-pools-*) echo $A/bridge-self/pools/${1#bridge-self-pools-}/gold;;
  bridge-self-pool) echo $A/bridge-self/pool/gold;;
  bridge-self-regress) echo $A/bridge-self/regress/gold;;
  bridge-self-micro) echo $A/bridge-self/micro/gold;;
  bridge-m413-respool) echo $A/bridge-m413/respool/gold;;
  bridge-m413-k) echo $A/bridge-m413/kgold;;
  bridge-m413-k2) echo $A/bridge-m413/k2gold;;
  cb-s974-merge) echo $A/cb-s974/fam-merge/gold;;
  cb-s974-vacuous) echo $A/cb-s974/fam-vacuous/gold;;
  bridge-reflexive-fam) echo $A/bridge-reflexive/fam/gold;;
  bridge-reflexive-seeds20) echo $A/bridge-reflexive/seeds20/gold;;
  bridge-nn-rule-red) echo $NNR;;
  bridge-satcache-red) echo $A/bridge-satcache/gold;;
  bridge-satcache-self) echo $A/bridge-satcache/selffix/gold;;
  *) echo UNKNOWN;; esac; }
grep -v '^#' $LIST | cut -f1,3 | sort -u | while IFS=$'\t' read pool route; do
  files=$(awk -F'\t' -v p=$pool -v r=$route '$1==p && $3==r {print $2}' $LIST)
  [ -z "$files" ] && continue
  python3 -I $S/tools/diff_run.py $BIN /nonexistent $(gold $pool) $OUT.$pool.part $route $files
  awk -v p=$pool 'BEGIN{OFS="\t"} {print p, $0}' $OUT.$pool.part >> $OUT; rm -f $OUT.$pool.part
done
