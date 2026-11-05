#!/bin/bash
# t1.sh BIN FILE ROUTE [K=V...] : one timed run, release flags, 60 s; prints rc, seconds, verdict vs gold if seven/gold has it.
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/bridge-nn-term; BIN=$1; f=$2; R=$3; shift 3
export TMPDIR=$S/tmp
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
RR=""; [ "$R" != auto ] && RR="KM_ROUTE=$R"
o=$S/dbg/t1.$$.json
s=$(date +%s.%N); env -i PATH=$PATH HOME=$HOME TMPDIR=$TMPDIR $F $RR "$@" timeout ${CAP:-60} $BIN classify $f > $o 2> $o.err; rc=$?
w=$(echo "$(date +%s.%N) - $s"|bc|cut -c1-6)
b=$(basename $f .ofn); v=""
if [ $rc = 0 ] && [ -f $S/seven/gold/$b.json ]; then v=$(python3 -I $S/tools/cmp1.py $S/seven/gold/$b.json $o); fi
echo -e "$b\t$R\t$*\trc=$rc\t$w\t$v"; rm -f $o $o.err
