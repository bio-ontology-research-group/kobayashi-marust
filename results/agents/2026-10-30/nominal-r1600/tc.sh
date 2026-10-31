#!/bin/bash
# tc.sh BIN FILE ROUTE CAP VARIANT... : classify wall time per variant
B=$1; F=$2; RT=$3; C=$4; shift 4
for v in "$@"; do s=$(date +%s.%N); if [ $RT = auto ]; then env -u KM_ROUTE $v timeout $C $B classify --lines $F > /dev/null 2>&1; else env $v KM_ROUTE=$RT timeout $C $B classify --lines $F > /dev/null 2>&1; fi; rc=$?; printf "%s\t%s\t%s\t%s\t%.2f\n" $(basename $F .ofn) $RT "$v" $rc $(echo "$(date +%s.%N)-$s"|bc); done
