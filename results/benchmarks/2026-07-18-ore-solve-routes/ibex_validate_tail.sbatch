#!/bin/bash
# Direct validation of the eight ORE inputs outside the 584 exact-gold set.
# Every array element owns one reasoner invocation and retains its raw output.
# Classification is capped at 240 s / 20 GiB; canonicalization runs afterwards.
#SBATCH --job-name=km-tail-validate
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --constraint=cpu_intel_gold_6248
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-30%12
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
validation=$root/tail-validation-20260718
runner=$validation/validate_tail_runner.py
canonicalize=$validation/canonicalize_tail_output.py
canonicalizer=$root/oracle/ore/ore_canon.py
corpus=$km_root/corpus
cores=$validation/cores

java=$km_root/bench/jdk8u492-b09/bin/java
elk=$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar
hermit_oracle=$km_root/bench/Oracle.class
hermit_classpath=$km_root/bench:$km_root/bench/hermit_cp/'*'
konclude=$km_root/Konclude-official

km_rules=$root/retained-route-rerun-20260718/target/release/km
km_giant=$km_root/14817_closure_20260714/km-14817-atleast
km_4669=$km_root/3215_closure_20260713/km-3215-bullseye
km_c229=$root/km-source-symbol-c229366f

task=${SLURM_ARRAY_TASK_ID:-0}
kind=
label=
ontology=
binary=
format=
workers=1
env_args=()

case "$task" in
  0) kind=km; label=km_ht_rules_2669; ontology=$corpus/ore_ont_2669.owl; binary=$km_rules; format=json; env_args+=(--env KM_HT_RULES=1) ;;
  1) kind=km; label=km_ht_rules_15516; ontology=$corpus/ore_ont_15516.owl; binary=$km_rules; format=json; env_args+=(--env KM_HT_RULES=1) ;;
  2) kind=km; label=km_production_3524; ontology=$corpus/ore_ont_3524.owl; binary=$km_giant; format=json; env_args+=(--env KM_TRIGGER_ABSORB=1 --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_BRIDGE_PROBE_BUDGET_S=30 --env KM_BRIDGE_RETRY_ROUNDS=0 --env KM_HT_SATURATION_BUDGET_S=180 --env KM_HT_MEM_GB=18 --env KM_PAR_MEM_GB=18 --env KM_THREADS=16) ;;
  3) kind=km; label=km_production_15703; ontology=$corpus/ore_ont_15703.owl; binary=$km_giant; format=json; env_args+=(--env KM_TRIGGER_ABSORB=1 --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_BRIDGE_PROBE_BUDGET_S=30 --env KM_BRIDGE_RETRY_ROUNDS=0 --env KM_HT_SATURATION_BUDGET_S=180 --env KM_HT_MEM_GB=18 --env KM_PAR_MEM_GB=18 --env KM_THREADS=16) ;;
  4) kind=km; label=km_production_4669; ontology=$corpus/ore_ont_4669.owl; binary=$km_4669; format=json; env_args+=(--env KM_TRIGGER_ABSORB=1 --env KM_KEEP_CHAIN_AXIOMS=1 --env KM_BRIDGE_PROBE_BUDGET_S=30 --env KM_BRIDGE_RETRY_ROUNDS=0 --env KM_HT_SATURATION_BUDGET_S=180 --env KM_HT_MEM_GB=18 --env KM_PAR_MEM_GB=18 --env KM_THREADS=16) ;;
  5) kind=km; label=km_ht_bridge_4669; ontology=$corpus/ore_ont_4669.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=ht_bridge) ;;
  6) kind=km; label=km_ht_full_4669; ontology=$corpus/ore_ont_4669.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=ht_full) ;;
  7) kind=km; label=km_production_c229_10621; ontology=$corpus/ore_ont_10621.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=production_all) ;;
  8) kind=km; label=km_production_c229_10860; ontology=$corpus/ore_ont_10860.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=production_all) ;;
  9) kind=km; label=km_production_c229_1194; ontology=$corpus/ore_ont_1194.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=production_all) ;;
  10) kind=km; label=km_cb_plain1_10621; ontology=$corpus/ore_ont_10621.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=cb_plain1) ;;
  11) kind=km; label=km_cb_plain1_10860; ontology=$corpus/ore_ont_10860.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=cb_plain1) ;;
  12) kind=km; label=km_ht_bridge_1194; ontology=$corpus/ore_ont_1194.owl; binary=$km_c229; format=json; env_args+=(--env KM_ROUTE=ht_bridge) ;;
  13) kind=hermit; label=hermit_core_2669; ontology=$cores/ore_ont_2669_norules.min.owl; binary=$hermit_oracle; format=json ;;
  14) kind=hermit; label=hermit_core_15516; ontology=$cores/ore_ont_15516_norules.min.owl; binary=$hermit_oracle; format=json ;;
  15) kind=hermit; label=hermit_core_10621; ontology=$cores/ore_ont_10621_functional-datatype.min.owl; binary=$hermit_oracle; format=json ;;
  16) kind=konclude; label=konclude_w16_3524; ontology=$corpus/ore_ont_3524.owl; binary=$konclude; format=owlxml; workers=16 ;;
  17) kind=hermit; label=hermit_3524; ontology=$corpus/ore_ont_3524.owl; binary=$hermit_oracle; format=json ;;
  18) kind=konclude; label=konclude_w16_15703; ontology=$corpus/ore_ont_15703.owl; binary=$konclude; format=owlxml; workers=16 ;;
  19) kind=hermit; label=hermit_15703; ontology=$corpus/ore_ont_15703.owl; binary=$hermit_oracle; format=json ;;
  20) kind=konclude; label=konclude_w16_4669; ontology=$corpus/ore_ont_4669.owl; binary=$konclude; format=owlxml; workers=16 ;;
  21) kind=hermit; label=hermit_4669; ontology=$corpus/ore_ont_4669.owl; binary=$hermit_oracle; format=json ;;
  22) kind=elk; label=elk_3524; ontology=$corpus/ore_ont_3524.owl; binary=$elk; format=functional ;;
  23) kind=elk; label=elk_15703; ontology=$corpus/ore_ont_15703.owl; binary=$elk; format=functional ;;
  24) kind=elk; label=elk_4669; ontology=$corpus/ore_ont_4669.owl; binary=$elk; format=functional ;;
  25) kind=hermit; label=hermit_10621; ontology=$corpus/ore_ont_10621.owl; binary=$hermit_oracle; format=json ;;
  26) kind=konclude; label=konclude_w16_10621; ontology=$corpus/ore_ont_10621.owl; binary=$konclude; format=owlxml; workers=16 ;;
  27) kind=hermit; label=hermit_10860; ontology=$corpus/ore_ont_10860.owl; binary=$hermit_oracle; format=json ;;
  28) kind=konclude; label=konclude_w16_10860; ontology=$corpus/ore_ont_10860.owl; binary=$konclude; format=owlxml; workers=16 ;;
  29) kind=hermit; label=hermit_1194; ontology=$corpus/ore_ont_1194.owl; binary=$hermit_oracle; format=json ;;
  30) kind=konclude; label=konclude_w16_1194; ontology=$corpus/ore_ont_1194.owl; binary=$konclude; format=owlxml; workers=16 ;;
  *) /usr/bin/printf 'invalid task %s\n' "$task" >&2; exit 2 ;;
esac

out=$validation/results/$label
/usr/bin/mkdir -p "$out" "$validation/slurm"

extra_args=()
case "$kind" in
  hermit) extra_args+=(--java "$java" --java-heap=-Xmx16g --classpath "$hermit_classpath") ;;
  elk) extra_args+=(--java "$java" --java-heap=-Xmx16g) ;;
  konclude) extra_args+=(--workers "$workers") ;;
esac

/usr/bin/python3 "$runner" \
  --kind "$kind" --label "$label" --ontology "$ontology" --binary "$binary" \
  --output-dir "$out" --timeout 240 --memcap-mb 20480 \
  "${extra_args[@]}" "${env_args[@]}"
run_rc=$?

primary=$out/stdout.log
if [[ "$kind" == elk || "$kind" == konclude ]]; then
  primary=$out/taxonomy.owl
fi

if [[ $run_rc -eq 0 && -s "$primary" ]]; then
  /usr/bin/timeout -k 10 600 /usr/bin/python3 "$canonicalize" \
    --canonicalizer "$canonicalizer" --input "$primary" --format "$format" \
    --output "$out/signature.sig.gz" > "$out/canonicalize.stdout" 2> "$out/canonicalize.stderr"
  canon_rc=$?
else
  canon_rc=125
fi

/usr/bin/python3 - "$out" "$label" "$task" "$run_rc" "$canon_rc" <<'PY'
import json
from pathlib import Path
import sys

out = Path(sys.argv[1])
summary = {
    "label": sys.argv[2],
    "task": int(sys.argv[3]),
    "runner_return_code": int(sys.argv[4]),
    "canonicalizer_return_code": int(sys.argv[5]),
}
run = out / "run.json"
canon = out / "signature.sig.gz.json"
if run.exists():
    summary["run"] = json.loads(run.read_text())
if canon.exists():
    summary["canonicalization"] = json.loads(canon.read_text())
tmp = out / "validation.json.tmp"
tmp.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
tmp.replace(out / "validation.json")
print(json.dumps(summary, sort_keys=True))
PY

/usr/bin/printf 'DONE label=%s task=%s run_rc=%s canon_rc=%s host=%s\n' \
  "$label" "$task" "$run_rc" "$canon_rc" "$(hostname)"
