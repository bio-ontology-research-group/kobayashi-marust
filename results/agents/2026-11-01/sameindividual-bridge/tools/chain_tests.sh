#!/bin/bash
# chain_tests.sh: seed differentials on km.v8, then the library and every integration target (--test-threads=1, KM_THREADS=1)
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sameindividual-bridge
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-sameindividual-bridge/engine
K=KM_HT_DDB=1,KM_HT_NATIVE_FULL=1,KM_CACHE_CONFORMANCE=1,KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1,KM_FAST_IRI_GRAMMAR=1,KM_THREADS=1
cd $S; export TMPDIR=$S/tmp
until [ -f $S/chain_v8.done ]; do sleep 20; done
DIFF_KM_TIMEOUT=30 DIFF_THREADS=2 DIFF_KEEP=$K python3 -I tools/diff_run.py $S/km.v8 $S/../../agent-assets/2026-10-28-scratch/oracle $S/gold diff/v8.tsv ht_bridge,auto $(ls seeds/s*.ofn | sort -V) > diff/v8.log 2>&1
DIFF_KM_TIMEOUT=30 DIFF_THREADS=2 DIFF_KEEP=$K python3 -I tools/diff_run.py $S/km.v8 $S/../../agent-assets/2026-10-28-scratch/oracle $S/cgold diff/chain-v8.tsv ht_bridge,auto $(ls cseeds/c*.ofn | sort -V) > diff/chain-v8.log 2>&1
echo SEEDS > $S/chain_tests.progress
cd $W
export KM_THREADS=1
CARGO_TARGET_DIR=$W/target nice cargo test --release --lib -- --test-threads=1 > $S/test-lib.log 2>&1
echo LIB > $S/chain_tests.progress
for t in tests/*.rs; do n=$(basename $t .rs)
  echo "=== $n" >> $S/test-int.log
  CARGO_TARGET_DIR=$W/target nice cargo test --release --test $n -- --test-threads=1 >> $S/test-int.log 2>&1
  echo "rc=$? $n" >> $S/test-int.log
done
echo DONE > $S/chain_tests.done
