#!/bin/bash
N=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/nominal-exchange
until [ -f $N/runs/drive3.done ]; do sleep 60; done
cd /mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/fix-nominal-exchange/engine
nice cargo test --release -j 12 --no-fail-fast --test merge_hypotheses --test r3_disjunctive_equality --test nominal_seq_order --test cb_route_completeness --test universal_role_and_top_data_range --test top_nominal_data_successors -- --test-threads=3 > $N/tests3.log 2>&1
echo TESTSDONE >> $N/tests3.log
