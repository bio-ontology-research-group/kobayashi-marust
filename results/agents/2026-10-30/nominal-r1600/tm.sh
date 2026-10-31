#!/bin/bash
# tm.sh BIN JSON CAP VARIANT... : engine-level wall time per variant
B=$1; J=$2; C=$3; shift 3
for v in "$@"; do s=$(date +%s.%N); env $v KM_NOMINALS=1 timeout $C $B engine < $J > /dev/null 2>&1; rc=$?; printf "%s\t%s\t%s\t%.2f\n" $(basename $J .json) "$v" $rc $(echo "$(date +%s.%N)-$s"|bc); done
