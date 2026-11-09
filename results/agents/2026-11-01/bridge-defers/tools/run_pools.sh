#!/bin/bash
# usage: run_pools.sh KM_BIN LABEL ROUTES
# Runs every data and nominal seed pool against its cached HermiT gold with
# diff_run.py (2 KM runs at a time, release flags, 60 s per run) and writes
# OUT/<pool>.<LABEL>.tsv under .work/agent-scratch/bridge-defers/diff.
set -u
KM=$1; LABEL=$2; ROUTES=$3
A=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch
OUT=$A/bridge-defers/diff; mkdir -p $OUT
ORACLE=$A/data-values/oracle
export DIFF_KEEP=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
export DIFF_THREADS=2 DIFF_KM_TIMEOUT=${DIFF_KM_TIMEOUT:-60}
run() { # pool seeds-dir gold-dir
  rm -f $OUT/$1.$LABEL.tsv
  python3 -I $(dirname $0)/diff_run.py $KM $ORACLE $3 $OUT/$1.$LABEL.tsv $ROUTES $2/*.ofn
}
run dec $A/bridge-defers/seeds $A/bridge-defers/gold
run dcr $A/data-coverage-regression/seeds $A/data-coverage-regression/gold-seeds
run nomcov $A/nominal-coverage/seeds $A/nominal-coverage/gold
run dvprobes $A/data-values/probes/gen $A/data-values/probes/gold
run fndm $A/forced-nominal-data-misses/fixtures $A/forced-nominal-data-misses/gold-fixtures
run tnd $A/top-nominal-data/fresh3 $A/top-nominal-data/gold_fresh3
run bnm $A/bridge-nominal-merge/seeds $A/bridge-nominal-merge/gold
