#!/bin/bash
# qbuild.sh NAME : fast (no LTO) release build in a separate target dir, copy to scratch/km.NAME
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/engine
if CARGO_TARGET_DIR=target-q CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_CODEGEN_UNITS=16 nice cargo build --release -j 12 --bin km > $S/qbuild-$1.log 2>&1; then
  cp target-q/release/km $S/km.$1; echo BUILT >> $S/qbuild-$1.log
else echo FAILED >> $S/qbuild-$1.log; fi
tail -1 $S/qbuild-$1.log
