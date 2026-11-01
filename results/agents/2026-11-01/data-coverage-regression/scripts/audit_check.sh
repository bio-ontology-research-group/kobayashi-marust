#!/bin/bash
# usage: audit_check.sh BIN NAME OUTDIR -- classify with KM_DT_AUDIT=1 for 90 s; count undecided datatype names
B=$1; n=$2; o=$3; f=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/$n.owl
mkdir -p $o
env KM_DT_AUDIT=1 KM_THREADS=1 KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 \
  TMPDIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/data-coverage-regression/tmp \
  timeout -s KILL 90 prlimit --as=$((20*1024*1024*1024)) -- $B classify --lines $f > $o/$n.out 2> $o/$n.err
echo "$n rc=$? undecided=$(grep -c 'KM_DT_AUDIT undecided' $o/$n.err) dropped=$(grep '^DROPPED' $o/$n.out)"
