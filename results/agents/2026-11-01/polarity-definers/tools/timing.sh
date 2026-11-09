#!/bin/bash
# timing.sh TAG : forced nominals wall time of the named seeds (60 s and 300 s) and of the object-value case, verdict vs HermiT
S=$S
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
V=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange/verdict.py
b=$1
one() { f=$1; cap=$2; t0=$(date +%s.%N); out=$(env -i PATH=$PATH HOME=$HOME KM_THREADS=1 KM_ROUTE=nominals timeout $cap $S/tools/pin-$b classify --lines $R/seeds/$f.ofn 2>/dev/null); rc=$?; t=$(echo "$(date +%s.%N)-$t0"|bc); printf "%s\t%s\t%s\t%s\t%.2f\t%s\n" $f $b $cap $rc $t "$(python3 -I $V $R/gold/$f.json <<< "$out")"; }
export -f one; export S R V b
printf "r163 60\nr219 60\nr461 60\nr481 60\nr575 60\nr696 60\nr1536 300\nr3777 300\n" | xargs -P 3 -L 1 bash -c 'one $0 $1'
