#!/bin/bash
# ore_nominal.sh BASE_BIN NEW_BIN : the 112 nominal ORE design-half inputs,
# base and new side by side (1 process each = 2 KM processes total), release flags, 300 s.
T=$(dirname "$(readlink -f "$0")")
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
O=$R/.work/agent-scratch/sat578-lost-argon/ore
D=$R/.work/worktrees/fix-sat578-lost-argon/results/agents/2026-11-09/sat578-lost-argon/data/nominal
LIST=$R/.work/worktrees/fix-bridge-nn-rule/results/agents/2026-11-04/bridge-nn-rule/tools/ore-design-nominal.txt
PAIR=$R/.work/worktrees/fix-sameindividual-bridge/results/agents/2026-11-01/sameindividual-bridge/tools/ore_pair.py
mkdir -p "$O" "$D"
rm -f "$O/times-before.tsv" "$O/times-after.tsv"
F="KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1"
"$T/ore_time.sh" "$1" "$LIST" "$O" before $F &
"$T/ore_time.sh" "$2" "$LIST" "$O" after $F &
wait
cp "$O/times-before.tsv" "$D/times-before.tsv"
cp "$O/times-after.tsv" "$D/times-after.tsv"
python3 -I "$PAIR" "$O" before after > "$D/pair.txt"
echo "guard fired (after): $(grep -l 'coverage guard fired' "$O/out-after/"*.errtail 2>/dev/null | wc -l)" >> "$D/pair.txt"
cat "$D/pair.txt"
