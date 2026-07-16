#!/bin/bash
# Regression gate for local-name collisions. Ontology 412 contains distinct
# full IRIs with identical local names, so canonicalization must collapse names
# before recomputing the SCC/transitive closure, exactly as the ORE gold path.
# The earlier shortcut closed full IRIs first and falsely reported 28 missing
# pairs for every KM arm.
#SBATCH --job-name=km-canon-412
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=00:15:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/canon-412-%j.out

set -euo pipefail
km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-final3
kon=$km_root/Konclude-official
ontology=ore_ont_412.owl
local_ontology=${SLURM_TMPDIR:-/tmp}/$ontology
/usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
gold=$km_root/gold/konclude__$ontology.sig.gz
work=${SLURM_TMPDIR:-/tmp}/km-canon-412-$SLURM_JOB_ID
result=$root/smoke-canonicalizer-412.jsonl
failure_dir=$root/smoke-canonicalizer-412-failures
mkdir -p "$work" "$failure_dir" "$root/slurm"
: > "$result"
km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)

/usr/bin/python3 "$runner" --kind konclude --arm konclude_w1 \
  --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
  --workers 1 --workdir "$work" --failures-dir "$failure_dir" \
  --timeout 240 --memcap-mb 20480 >> "$result"
/usr/bin/python3 "$runner" --kind km --arm production_all \
  --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha" \
  --gold "$gold" --workdir "$work" --failures-dir "$failure_dir" \
  --timeout 240 --memcap-mb 20480 --env KM_ROUTE=production_all >> "$result"
/usr/bin/python3 "$runner" --kind konclude --arm konclude_w16 \
  --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
  --workers 16 --workdir "$work" --failures-dir "$failure_dir" \
  --timeout 240 --memcap-mb 20480 >> "$result"

/usr/bin/python3 - "$result" <<'PY'
import json
import sys

expected_canon = "2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2"
rows = {row["arm"]: row for row in map(json.loads, open(sys.argv[1]))}
assert set(rows) == {"konclude_w1", "production_all", "konclude_w16"}
assert {row.get("canonicalizer_sha256") for row in rows.values()} == {expected_canon}
assert all(rows[arm].get("status") == "ok" and rows[arm].get("verdict") == "reference"
           for arm in ("konclude_w1", "konclude_w16"))
km = rows["production_all"]
assert km.get("status") == "ok" and km.get("verdict") == "match", km
assert all(km.get(key) == 0 for key in
           ("extra", "missing", "extra_unsat", "missing_unsat")), km
assert km.get("consistency_mismatch") is False, km
PY

/usr/bin/rm -rf "$work" "$local_ontology"
/usr/bin/printf 'DONE ontology=%s rows=3 km_sha=%s canon_sha=%s host=%s\n' \
  "$ontology" "$km_sha" \
  2fc28764e34418ae3004f6dca7bb9bb6c6f763b022b0d356b80f896fa18173a2 \
  "$(hostname)"
