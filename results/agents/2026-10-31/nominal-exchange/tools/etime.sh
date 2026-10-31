#!/bin/bash
# etime.sh BIN CAP VARIANT SEED... : engine-level wall time on captured nominals-route inputs (j/<seed>n.json), KM_THREADS=1
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
B=$1; C=$2; V=$3; shift 3
for f in "$@"; do s=$(date +%s.%N); env $(cat $N/route.env) $V KM_THREADS=1 timeout $C $B engine < $N/j/${f}n.json > /dev/null 2>&1; rc=$?; printf "%s\t%s\t%s\t%.2f\n" $f "$V" $rc $(echo "$(date +%s.%N)-$s"|bc); done
