#!/bin/bash
# one.sh BIN N LABEL [extra env...] : one ORE input, release flags, 240 s, RSS.
R=/mnt/data2/workspaces/leechuck/software/kobayashi-marust
S=$R/.work/agent-scratch/sat578-lost-argon/heldout
D=$R/.work/worktrees/fix-sat578-lost-argon/results/agents/2026-11-09/sat578-lost-argon/data/heldout
mkdir -p "$S" "$D"
BIN=$1; n=$2; L=$3; shift 3
export KM_HT_DDB=1 KM_HT_NATIVE_FULL=1 KM_CACHE_CONFORMANCE=1 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE=1 KM_FAST_IRI_GRAMMAR=1 KM_THREADS=1
for kv in "$@"; do export "$kv"; done
CMP=$R/.work/worktrees/fix-bridge-defers/results/agents/2026-11-01/bridge-defers/tools/compare_ref.py
s=$(date +%s.%N)
/usr/bin/time -v -o "$S/$n.$L.time" timeout -k 5 "${CAP:-240}" "$BIN" classify "$R/v150-corpus/files/ore_ont_$n.owl" > "$S/$n.$L.json" 2> "$S/$n.$L.err"
rc=$?
w=$(echo "$(date +%s.%N) - $s" | bc | cut -c1-6)
rss=$(awk '/Maximum resident/ {printf "%.2f", $NF/1048576}' "$S/$n.$L.time")
agree=""
if [ "$rc" = 0 ]; then
  agree=$(python3 -I "$CMP" "ore_ont_$n" "$S/$n.$L.json" "$S/cmp-$n-$L" 2>&1 | grep -oE '"reference": "[a-z]+", "status": "[a-z_]+"' | sed 's/"reference": //; s/, "status": /=/; s/"//g' | tr '\n' ' ')
fi
echo -e "$n\t$L\trc=$rc\twall=$w\trss_gib=$rss\t$agree" | tee -a "$D/summary.tsv"
