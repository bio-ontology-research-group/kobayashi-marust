#!/bin/bash
# campaign2.sh: one KM run at a time. Fixtures (9, both routes, 3 runs) on the
# fix and once on the base; the regression rows of fbd1932c 3 times; the 20 s
# pool timeouts at 60 s on the fix (with guard markers).
S=/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/agent-scratch/sat578-opus
FIX=$S/bin/km-b1fcbb93; BASE=$S/bin/km-274faa6a
cd $S; export TMPDIR=$S/tmp FAM_THREADS=1 FAM_TIMEOUT=60 FAM_FORCED_TIMEOUT=60
rm -f data/fx-final.tsv data/fx-base.tsv data/reg-final.tsv
python3 -I tools/fam_run.py $FIX fxgold data/fx-final.tsv ht_bridge,auto 3 fx/*.ofn
python3 -I tools/fam_run.py $BASE fxgold data/fx-base.tsv ht_bridge,auto 1 fx/*.ofn
sed -i 's/DIFF_THREADS=2/DIFF_THREADS=${DIFF_THREADS:-1}/' tools/reg.sh
DIFF_THREADS=1 tools/reg.sh $FIX data/reg-final.tsv 3 > logs/reg-final.log 2>&1
mkdir -p runs/fired-cap60; rm -f runs/fix-cap60.tsv
DIFF_THREADS=1 DIFF_GUARD_DIR=$S/runs/fired-cap60 tools/rows.sh $FIX runs/cap20-timeouts.tsv runs/fix-cap60.tsv 60 > logs/fix-cap60.log 2>&1
echo DONE > logs/campaign2.done
