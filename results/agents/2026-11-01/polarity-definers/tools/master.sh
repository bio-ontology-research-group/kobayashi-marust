#!/bin/bash
# master.sh: the validation sequence after the frontend differential, at most 3 KM runs at a time
S=$S
W=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-polarity-definers
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/r3-unannounced
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
cd $S
until grep -q DONE fe-ore.err; do sleep 30; done
echo "fe done $(date)" >> master.log
# 1. integration tests
(cd $W/engine && KM_THREADS=1 nice cargo test --release -j 12 --no-fail-fast \
  --test universal_role_and_top_data_range --test native_data_values --test top_nominal_data_successors \
  --test merge_hypotheses --test nominal_seq_order --test cb_route_completeness --test rule_taxonomy_nominal \
  --test source_module_reuse --test incremental_ht_reasoning -- --test-threads=3 > $S/tests-integration.txt 2>&1)
echo "tests done $(date)" >> master.log
# 2. ORE classify of changed inputs, base and new
awk -F'\t' '$3!=$4 || $5!=$6 {print $1}' fe-ore.tsv | sort -u > ore-changed.txt
grep -F -f <(sed 's/$/./' ore-changed.txt) ore-list.txt > ore-changed-paths.txt
for b in new base; do sed "s/^/$b /" ore-changed-paths.txt; done | xargs -P 3 -L 1 ./tools/ore_cls.sh > ore-cls.tsv 2> ore-cls.err
echo "ore done $(date)" >> master.log
# 3. timings
./tools/timing.sh base > timing-base.tsv; ./tools/timing.sh new > timing-new.tsv
echo "timing done $(date)" >> master.log
# 4. seeds
./tools/runset.sh tools/pin-new runs/new-rand1k-nominals-60.tsv 60 nominals $N/list-rand1k.txt
./tools/runset.sh tools/pin-new runs/new-rand-nominals-10.tsv 10 nominals $N/list-rand.txt
./tools/runset.sh tools/pin-new runs/new-rand-auto-10.tsv 10 auto $N/list-rand.txt
echo "seeds done $(date)" >> master.log
# 5. data-value pools
./tools/dataset.sh new probes fixtures tnd-sorts tnd-fresh2 tnd-fresh3 nomdata-forced nomdata-auto r3data-auto r1600-auto > runs/dataset-new.log 2>&1
echo "ALLDONE $(date)" >> master.log
