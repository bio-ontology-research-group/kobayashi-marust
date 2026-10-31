#!/bin/bash
# build.sh NAME : release build of km in the worktree, copy to scratch/km.NAME
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/engine
for i in 1 2 3 4 5; do
  if nice cargo build --release -j 12 --bin km > $S/build-$1.log 2>&1; then
    cp target/release/km $S/km.$1; echo BUILT >> $S/build-$1.log; exit 0
  fi
  grep -q "^error" $S/build-$1.log && { echo FAILED >> $S/build-$1.log; exit 1; }
  sleep 30
done
echo FAILED >> $S/build-$1.log
