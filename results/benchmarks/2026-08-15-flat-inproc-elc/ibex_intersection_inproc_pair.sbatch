#!/bin/bash
#SBATCH --job-name=km-intersection-inproc-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --time=00:12:00
#SBATCH --array=0-1
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/intersection-inproc-20260815/pair-%A_%a.out

set -euo pipefail
ids=(10806 9590)
id=${ids[$SLURM_ARRAY_TASK_ID]}
root=/ibex/scratch/hohndor/km/intersection-inproc-20260815
harness=/ibex/scratch/hohndor/km/intersection-el-route-20260815/full-sweep
km_root=/ibex/scratch/hohndor/km
mkdir -p "$root/pair" "$root/pair/failures"
for arm in baseline candidate; do
    binary=/ibex/scratch/hohndor/km/intersection-el-route-20260815/km
    [[ $arm == candidate ]] && binary=$root/km
    sha=$(sha256sum "$binary" | cut -d' ' -f1)
    work=${SLURM_TMPDIR:-/tmp}/km-intersection-inproc-${id}-${arm}
    /usr/bin/python3 "$harness/full_panel_run_one.py" \
      --kind km --arm "$arm" \
      --ontology "$km_root/corpus/ore_ont_${id}.owl" \
      --binary "$binary" --binary-sha "$sha" --workers 16 \
      --timeout 240 --memcap-mb 20480 \
      --gold "$km_root/cmp2/out/konclude/konclude__ore_ont_${id}.owl.sig.gz" \
      --gold-kind konclude --workdir "$work" \
      --failures-dir "$root/pair/failures" --capture-km-route \
      --env KM_ROUTE=auto > "$root/pair/${id}-${arm}.json"
done
/usr/bin/python3 - "$root/pair/${id}-baseline.json" "$root/pair/${id}-candidate.json" <<'PY'
import json
import sys
b, c = (json.load(open(path)) for path in sys.argv[1:])
for field in ("status", "verdict", "consistent", "signature_sha256"):
    if b.get(field) != c.get(field):
        raise SystemExit(f"{field} differs: {b.get(field)!r} != {c.get(field)!r}")
print(
    "PAIR_OK",
    b["ont"],
    f"wall={b['wall_s']}->{c['wall_s']}",
    f"rss={b['peak_mb']}->{c['peak_mb']}",
    f"route={b['selected_route_trace']}->{c['selected_route_trace']}",
)
PY
