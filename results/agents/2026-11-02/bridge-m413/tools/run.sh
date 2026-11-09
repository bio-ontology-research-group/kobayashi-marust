#!/bin/bash
# usage: run.sh BIN ONT [ENV=VAL ...]: one km classify --lines run, release flags, 240 s.
bin=$1; ont=$2; shift 2
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-m413
mkdir -p $S/tmp
env TMPDIR=$S/tmp KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 \
  KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1 "$@" \
  timeout 240 $bin classify --lines $ont
