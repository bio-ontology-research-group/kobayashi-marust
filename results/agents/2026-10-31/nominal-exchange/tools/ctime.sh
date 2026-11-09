#!/bin/bash
# ctime.sh BIN CAP VARIANT SEED... : forced-nominals classify wall time and verdict vs HermiT for attr/<seed>.ofn
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
B=$1; C=$2; V=$3; shift 3
for f in "$@"; do s=$(date +%s.%N); out=$(env $V KM_ROUTE=${ROUTE:-nominals} timeout $C $B classify --lines $N/attr/$f.ofn 2>/dev/null); rc=$?; t=$(echo "$(date +%s.%N)-$s"|bc)
v=$(python3 -I $N/verdict.py $N/attr/$f.hermit.json <<< "$out"); printf "%s\t%s\t%s\t%.2f\t%s\n" $f "$V" $rc $t "$v"; done
