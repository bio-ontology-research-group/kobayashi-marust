#!/bin/bash
#SBATCH --job-name=km-3215-eqcache-pair
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --nodes=1
#SBATCH --exclusive
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=24G
#SBATCH --export=NONE
#SBATCH --output=/ibex/scratch/hohndor/km/3215-equivalent-cache-20260815/pair-%j.out

set -euo pipefail
root=/ibex/scratch/hohndor/km/3215-equivalent-cache-20260815
harness=/ibex/scratch/hohndor/km/candidate-6682-auto-probe-20260813
baseline=/ibex/scratch/hohndor/km/6934-general-isolation-20260814/km
candidate=$root/km
baseline_sha=4d8d81378d565d6b5d0b33b8fe352d2e6aa076b7c82a0c196bb58bc167401071
candidate_sha=$(cut -d' ' -f1 < "$root/km.sha256")
ont=ore_ont_3215.owl
mkdir -p "$root/pair-results" "$root/failures"
[[ $(sha256sum "$baseline" | cut -d' ' -f1) == "$baseline_sha" ]]
[[ $(sha256sum "$candidate" | cut -d' ' -f1) == "$candidate_sha" ]]
cpu_model=$(/usr/bin/awk -F: '/model name/{sub(/^[ \t]+/, "", $2); print $2; exit}' /proc/cpuinfo)
[[ $cpu_model == *"Intel(R) Xeon(R) Gold 6248 CPU @ 2.50GHz"* ]]
work=${SLURM_TMPDIR:-/tmp}/km-3215-eqcache-pair-$SLURM_JOB_ID

for spec in '0 baseline' '0 candidate' '1 candidate' '1 baseline'; do
  read -r rep label <<< "$spec"
  binary=$baseline; expected=$baseline_sha
  if [[ $label == candidate ]]; then binary=$candidate; expected=$candidate_sha; fi
  out="$root/pair-results/${rep}-${label}-${SLURM_JOB_ID}.json"
  /usr/bin/python3 "$harness/full_panel_run_one.py" \
    --kind km --arm "3215_eqcache_${rep}_${label}" \
    --ontology "/ibex/scratch/hohndor/km/corpus/$ont" \
    --binary "$binary" --workers 16 --timeout 240 --memcap-mb 20480 \
    --gold "/ibex/scratch/hohndor/km/cmp2/out/konclude/konclude__$ont.sig.gz" \
    --gold-kind konclude --workdir "$work/$rep-$label" \
    --failures-dir "$root/failures" --checkpoint "$out.checkpoint.json" \
    --capture-km-route --env KM_ROUTE=auto > "$out.tmp"
  /usr/bin/python3 - "$out.tmp" "$expected" <<'PY'
import json,sys
r=json.load(open(sys.argv[1]))
assert r["binary_sha256"] == sys.argv[2]
assert r["checkpointed"] and r["status"] == "ok" and r["verdict"] == "match", r
assert r["selected_route_trace"] == "production_all", r
PY
  mv "$out.tmp" "$out"
done

/usr/bin/python3 - "$root/pair-results" "$SLURM_JOB_ID" <<'PY'
import glob,json,statistics,sys
root,job=sys.argv[1:]
rows=[json.load(open(p)) for p in glob.glob(f"{root}/*-*-{job}.json")]
assert len(rows)==4
for label in ("baseline","candidate"):
    q=[r for r in rows if r["arm"].endswith(label)]
    print(label, json.dumps({
      "wall_mean":statistics.mean(r["wall_s"] for r in q),
      "peak_mean":statistics.mean(r["peak_mb"] for r in q),
      "signature":q[0]["signature_sha256"],
    },sort_keys=True))
assert len({r["signature_sha256"] for r in rows}) == 1
PY
echo PAIR_COMPLETE
