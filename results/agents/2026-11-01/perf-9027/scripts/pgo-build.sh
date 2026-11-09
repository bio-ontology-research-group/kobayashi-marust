#!/bin/bash
# Release-equivalent build: LTO, one codegen unit, mimalloc, the v1.5.5 preview PGO profile.
cd ${SRC:-/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-perf-9027/engine}
export CARGO_TARGET_DIR=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-perf-9027/engine/target-pgo CARGO_PROFILE_RELEASE_LTO=true CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 CARGO_BUILD_JOBS=12
export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.5/tools/release/v155/cc-wrapper.sh
export RUSTFLAGS="-Cprofile-use=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/pgo-v155-preview/merged.profdata"
nice cargo build --offline --locked --release --target=x86_64-unknown-linux-gnu --features mimalloc --bin km 2>&1 | grep -E '^error|Finished' -A5
cp $CARGO_TARGET_DIR/x86_64-unknown-linux-gnu/release/km /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/perf-9027/km.pgo.$1
