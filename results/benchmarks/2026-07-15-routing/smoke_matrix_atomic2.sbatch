#!/bin/bash
# Command-line, canonicalization, and provenance gate for every external
# baseline plus the repaired trigger and composite HT mechanisms.
#SBATCH --job-name=km-matrix-smoke
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --exclusive
#SBATCH --time=02:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/slurm/smoke-atomic3-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
runner=$root/bench_one_matrix_frozen.py
km=$root/km-profiled-atomic2
kon=$km_root/Konclude-official
bench=$km_root/bench
java=$bench/jdk8u492-b09/bin/java
elk=$bench/reasoners/elk-distribution-cli-0.6.0/elk.jar
hermit_oracle=$bench/Oracle.class
hermit_main=$bench/hermit_cp/org.semanticweb.hermit-1.4.6.519-SNAPSHOT.jar
hermit_classpath=$bench:$bench/hermit_cp/'*'
failure_dir=$root/failures-smoke-atomic3
result=$root/smoke-atomic3-${SLURM_JOB_ID}.jsonl
nogold_result=$root/smoke-nogold-atomic3-${SLURM_JOB_ID}.jsonl
work=${SLURM_TMPDIR:-/tmp}/km-smoke-${SLURM_JOB_ID}
/usr/bin/mkdir -p "$work" "$failure_dir" "$root/slurm"
: > "$result"
: > "$nogold_result"

km_sha=$(/usr/bin/sha256sum "$km" | /usr/bin/cut -d' ' -f1)
kon_sha=$(/usr/bin/sha256sum "$kon" | /usr/bin/cut -d' ' -f1)
elk_sha=$(/usr/bin/sha256sum "$elk" | /usr/bin/cut -d' ' -f1)
java_sha=$(/usr/bin/sha256sum "$java" | /usr/bin/cut -d' ' -f1)
hermit_sha=$(
  {
    /usr/bin/sha256sum "$hermit_oracle"
    /usr/bin/find "$bench/hermit_cp" -maxdepth 1 -type f -name '*.jar' -print0 \
      | /usr/bin/sort -z | /usr/bin/xargs -0 /usr/bin/sha256sum
  } | /usr/bin/sha256sum | /usr/bin/cut -d' ' -f1
)

for ont_id in 703 9509; do
  ontology=ore_ont_${ont_id}.owl
  local_ontology=$work/$ontology
  /usr/bin/cp "$km_root/corpus/$ontology" "$local_ontology"
  gold=$km_root/gold/konclude__$ontology.sig.gz
  position=0
  for route in cb_trigger16 ht_bridge ht_features ht_full; do
    /usr/bin/python3 "$runner" --kind km --arm "$route" \
      --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha" \
      --gold "$gold" --gold-kind konclude \
      --workdir "$work" --failures-dir "$failure_dir" \
      --order-index "$position" --timeout 120 --memcap-mb 20480 \
      --env "KM_ROUTE=$route" >> "$result"
    position=$((position + 1))
  done
  /usr/bin/python3 "$runner" --kind elk --arm elk \
    --ontology "$local_ontology" --binary "$elk" --binary-sha "$elk_sha" \
    --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
    --gold "$gold" --gold-kind konclude \
    --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$position" --timeout 120 --memcap-mb 20480 >> "$result"
  position=$((position + 1))
  /usr/bin/python3 "$runner" --kind hermit --arm hermit \
    --ontology "$local_ontology" --binary "$hermit_oracle" --binary-sha "$hermit_sha" \
    --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
    --classpath "$hermit_classpath" \
    --gold "$gold" --gold-kind konclude \
    --workdir "$work" --failures-dir "$failure_dir" \
    --order-index "$position" --timeout 120 --memcap-mb 20480 >> "$result"
  position=$((position + 1))
  for workers in 1 16; do
    /usr/bin/python3 "$runner" --kind konclude --arm "konclude_w${workers}" \
      --ontology "$local_ontology" --binary "$kon" --binary-sha "$kon_sha" \
      --workers "$workers" --gold "$gold" --gold-kind konclude --workdir "$work" \
      --failures-dir "$failure_dir" --order-index "$position" \
      --timeout 120 --memcap-mb 20480 >> "$result"
    position=$((position + 1))
  done
done

# Exercise the no-gold runner/adjudicator path on a fast ontology with the gold
# deliberately withheld. This is an integration test only; the full matrix
# uses no-gold mode exclusively for the five names frozen in matrix_contract.py.
ontology=ore_ont_703.owl
local_ontology=$work/$ontology
/usr/bin/python3 "$runner" --kind km --arm cb_trigger16 \
  --ontology "$local_ontology" --binary "$km" --binary-sha "$km_sha" \
  --gold-kind none --workdir "$work" --failures-dir "$failure_dir" \
  --order-index 0 --timeout 120 --memcap-mb 20480 \
  --env KM_ROUTE=cb_trigger16 >> "$nogold_result"
/usr/bin/python3 "$runner" --kind hermit --arm hermit \
  --ontology "$local_ontology" --binary "$hermit_oracle" --binary-sha "$hermit_sha" \
  --java "$java" --runtime-sha "$java_sha" --java-heap=-Xmx16g \
  --classpath "$hermit_classpath" --gold-kind none \
  --workdir "$work" --failures-dir "$failure_dir" \
  --order-index 1 --timeout 120 --memcap-mb 20480 >> "$nogold_result"

/usr/bin/python3 - "$result" "$nogold_result" "$root" <<'PY'
import json
import sys

rows = [json.loads(line) for line in open(sys.argv[1]) if line.strip()]
assert len(rows) == 16, len(rows)
by_key = {(row["ont"], row["arm"]): row for row in rows}
assert len(by_key) == 16
for ont in ("ore_ont_703.owl", "ore_ont_9509.owl"):
    hashes = set()
    for arm in (
        "cb_trigger16", "ht_bridge", "ht_features", "ht_full",
        "elk", "hermit", "konclude_w1", "konclude_w16",
    ):
        assert by_key[(ont, arm)]["verdict"] == "match", by_key[(ont, arm)]
        assert by_key[(ont, arm)]["gold_kind"] == "konclude"
        assert by_key[(ont, arm)]["gold_basename"] == f"konclude__{ont}.sig.gz"
        assert by_key[(ont, arm)]["gold_sha256"]
        assert by_key[(ont, arm)]["signature_sha256"]
        hashes.add(by_key[(ont, arm)]["signature_sha256"])
    assert len(hashes) == 1, (ont, hashes)

nogold = [json.loads(line) for line in open(sys.argv[2]) if line.strip()]
assert len(nogold) == 2, nogold
assert all(row["verdict"] == "nogold" for row in nogold), nogold
assert all(row["solved"] is False for row in nogold), nogold
assert all(row["gold_kind"] == "none" for row in nogold), nogold
assert all(row["gold_basename"] is None for row in nogold), nogold
assert len({row["signature_sha256"] for row in nogold}) == 1, nogold
sys.path.insert(0, sys.argv[3])
from analyze_matrix import adjudicate_missing_konclude_gold
matrix = {"ore_ont_703.owl": {row["arm"]: row for row in nogold}}
adjudicated, unadjudicated = adjudicate_missing_konclude_gold(matrix)
assert not unadjudicated, unadjudicated
assert adjudicated[0]["matches"] == 2, adjudicated
assert all(row["verdict"] == "match_hermit" for row in matrix["ore_ont_703.owl"].values())
print(json.dumps(rows, indent=2, sort_keys=True))
PY
