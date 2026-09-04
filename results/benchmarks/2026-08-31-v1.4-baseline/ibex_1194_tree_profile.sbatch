#!/bin/bash
#SBATCH --job-name=km-v14-1194-phases
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodelist=cn512-15-r
#SBATCH --cpus-per-task=16
#SBATCH --mem=28G
#SBATCH --time=00:06:00
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/v1.4.0-combined-candidate-20260901/tree-profile-phases2/slurm-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/v1.4.0-combined-candidate-20260901/tree-profile-phases2
binary=/ibex/scratch/hohndor/km/v1.4.0-combined-candidate-20260901/km
expected=8a3309100dba66124d3b4578b8cf2b3c465d990b1294322d9d6e9034a496bdfa
ontology=/ibex/scratch/hohndor/km/corpus/ore_ont_1194.owl
mkdir -p "$root"
[[ $(sha256sum "$binary" | cut -d' ' -f1) == "$expected" ]]

set +e
env KM_ROUTE=auto KM_TIMING=1 KM_BRIDGE_PHASES=1 KM_HT_STATS=1 \
  "$binary" classify "$ontology" \
  > "$root/classification.json.tmp" 2> "$root/stderr.txt.tmp" &
leader=$!
set -e
while kill -0 "$leader" 2>/dev/null; do
  python3 - "$leader" >> "$root/process-rss.tsv.tmp" <<'PY'
import pathlib, sys, time
root = int(sys.argv[1])
rows = {}
for stat in pathlib.Path('/proc').glob('[0-9]*/stat'):
    try:
        fields = stat.read_text().split()
        pid, ppid = int(fields[0]), int(fields[3])
        rss = int(pathlib.Path(f'/proc/{pid}/statm').read_text().split()[1]) * 4
        cmd = pathlib.Path(f'/proc/{pid}/comm').read_text().strip()
        rows[pid] = (ppid, rss, cmd)
    except (FileNotFoundError, ProcessLookupError, PermissionError, ValueError):
        pass
members = {root}
changed = True
while changed:
    changed = False
    for pid, (ppid, _, _) in rows.items():
        if ppid in members and pid not in members:
            members.add(pid); changed = True
stamp = time.monotonic()
for pid in sorted(members):
    if pid in rows:
        ppid, rss, cmd = rows[pid]
        print(f'{stamp:.3f}\t{pid}\t{ppid}\t{rss}\t{cmd}')
print(f'{stamp:.3f}\tTOTAL\t-\t{sum(rows[p][1] for p in members if p in rows)}\t-')
PY
  sleep 2
done
set +e
wait "$leader"
rc=$?
set -e
mv "$root/process-rss.tsv.tmp" "$root/process-rss.tsv"
mv "$root/stderr.txt.tmp" "$root/stderr.txt"
if [[ $rc -eq 0 ]]; then
  mv "$root/classification.json.tmp" "$root/classification.json"
else
  unlink "$root/classification.json.tmp"
fi
echo "rc=$rc"
awk -F '\t' '$2=="TOTAL" && $4>peak {peak=$4; line=$0} END {print "peak_total_kib=" peak; print line}' "$root/process-rss.tsv"
awk -F '\t' '$2!="TOTAL" {key=$5; if ($4>peak[key]) peak[key]=$4} END {for (key in peak) print "peak_process_kib",key,peak[key]}' "$root/process-rss.tsv" | sort
grep -E 'KM_TIMING' "$root/stderr" || true
