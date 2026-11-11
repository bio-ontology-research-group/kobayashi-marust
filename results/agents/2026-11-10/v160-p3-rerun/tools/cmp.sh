#!/bin/bash
# usage: cmp.sh file...
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v160-nary-conjunction
for f in "$@"; do
 a=$(env -i PATH=$PATH HOME=$HOME KM_THREADS=1 KM_REFERENCE_STAGE=0 timeout 300 $W/engine/target/release/km classify --route auto $f --lines 2>/dev/null | sort | sha256sum | cut -c1-12)
 b=$(env -i PATH=$PATH HOME=$HOME KM_THREADS=1 KM_TIMING=1 KM_REFERENCE_FORCE=1 KM_EL_REFERENCE_CHECKER=$W/lean/.lake/build/bin/km-el-reference LEAN_STACK_SIZE_KB=262144 timeout 300 $W/engine/target/release/km classify --route auto $f --lines 2>$W/../../agent-scratch/v160-p3-rerun/err.txt | sort | sha256sum | cut -c1-12)
 echo "$(basename $f) unforced=$a forced=$b $([ $a = $b ] && echo OK || echo DIFF) $(grep -o 'REFERENCE_STAGE.*' $W/../../agent-scratch/v160-p3-rerun/err.txt | head -1)"
done
