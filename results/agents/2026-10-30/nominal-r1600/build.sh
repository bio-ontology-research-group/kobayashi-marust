#!/bin/bash
# build.sh NAME : release build of km in the worktree with retries (SIGABRT under the commit limit), copy to scratch/NAME
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-r1600/engine
for i in 1 2 3 4 5; do
  if nice cargo build --release -j 8 --bin km > /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/build-$1.log 2>&1; then
    cp target/release/km /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/km.$1; echo BUILT >> /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/build-$1.log; exit 0
  fi
  grep -q "^error\[" /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/build-$1.log && { echo FAILED >> /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/build-$1.log; exit 1; }
  sleep 30
done
echo FAILED >> /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-r1600/build-$1.log
