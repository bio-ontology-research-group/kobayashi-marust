#!/bin/bash
# htg.sh FILE [ENV=VAL...] : ht_general bundle under KM_ROUTE=manual, extra env allowed
f=$1; shift
exec env KM_ROUTE=manual KM_THREADS=16 KM_PAR_MEM_GB=18 KM_HT_MEM_GB=18 KM_KEEP_CHAIN_AXIOMS=1 KM_MECHANISM=ht KM_NO_ELC=1 KM_NO_HT_RULES=1 KM_NO_ABSORB_PORTFOLIO=1 KM_ABSORB=0 KM_NO_HT_QO_ROUTER=1 KM_NO_HT_SHOQ=1 KM_NO_HT_CARD=1 KM_HT_ONLY=general KM_HT_FORCE=1 KM_HT_NICE=0 "$@" ${KM:-/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/ht-card-complement/km-fix-share} classify --lines $f
