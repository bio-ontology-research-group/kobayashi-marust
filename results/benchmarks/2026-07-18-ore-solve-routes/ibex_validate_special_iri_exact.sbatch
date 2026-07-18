#!/bin/bash
# Revalidate exact-gold rows whose legal source class collides with Thing/Nothing.
#SBATCH --job-name=km-special-iri
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:10:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=22G
#SBATCH --array=0-5%6
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/tail-validation-20260718/slurm/special-iri-%A_%a.out

set -u

km_root=/ibex/scratch/hohndor/km
root=$km_root/routing_20260715
validation=$root/tail-validation-20260718
runner=$validation/validate_tail_runner.py
canonicalize=$validation/canonicalize_tail_output.py
canonicalizer=$root/oracle/ore/ore_canon.py
corpus=$km_root/corpus
java=$km_root/bench/jdk8u492-b09/bin/java
hermit=$km_root/bench/Oracle.class
hermit_classpath=$km_root/bench:$km_root/bench/hermit_cp/'*'
konclude=$km_root/Konclude-official
km_7581=$root/candidates/a0d0148816c5/km
km_13503=$root/candidate-a068059/km

task=${SLURM_ARRAY_TASK_ID:-0}
kind=
label=
ontology=
binary=
format=
extra=()
env_args=()
case "$task" in
  0) kind=km; label=km_fulliri_audit_7581; ontology=$corpus/ore_ont_7581.owl; binary=$km_7581; format=json; env_args+=(--env KM_ROUTE=production_all) ;;
  1) kind=konclude; label=konclude_fulliri_audit_7581; ontology=$corpus/ore_ont_7581.owl; binary=$konclude; format=owlxml; extra+=(--workers 16) ;;
  2) kind=hermit; label=hermit_fulliri_audit_7581; ontology=$corpus/ore_ont_7581.owl; binary=$hermit; format=json; extra+=(--java "$java" --java-heap=-Xmx16g --classpath "$hermit_classpath") ;;
  3) kind=km; label=km_fulliri_audit_13503; ontology=$corpus/ore_ont_13503.owl; binary=$km_13503; format=json; env_args+=(--env KM_ROUTE=production_all) ;;
  4) kind=konclude; label=konclude_fulliri_audit_13503; ontology=$corpus/ore_ont_13503.owl; binary=$konclude; format=owlxml; extra+=(--workers 16) ;;
  5) kind=hermit; label=hermit_fulliri_audit_13503; ontology=$corpus/ore_ont_13503.owl; binary=$hermit; format=json; extra+=(--java "$java" --java-heap=-Xmx16g --classpath "$hermit_classpath") ;;
  *) exit 2 ;;
esac

out=$validation/results/$label
/usr/bin/mkdir -p "$out"
/usr/bin/python3 "$runner" \
  --kind "$kind" --label "$label" --ontology "$ontology" --binary "$binary" \
  --output-dir "$out" --timeout 240 --memcap-mb 20480 \
  "${extra[@]}" "${env_args[@]}"
run_rc=$?

primary=$out/stdout.log
if [[ "$kind" == konclude ]]; then
  primary=$out/taxonomy.owl
fi
if [[ $run_rc -eq 0 && -s "$primary" ]]; then
  /usr/bin/timeout -k 10 300 /usr/bin/python3 "$canonicalize" \
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
for key, name in (("run", "run.json"), ("canonicalization", "signature.sig.gz.json")):
    path = out / name
    if path.exists():
        summary[key] = json.loads(path.read_text())
temporary = out / "validation.json.tmp"
temporary.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
temporary.replace(out / "validation.json")
print(json.dumps(summary, sort_keys=True))
PY

/usr/bin/printf 'DONE label=%s run_rc=%s canon_rc=%s host=%s\n' \
  "$label" "$run_rc" "$canon_rc" "$(hostname)"
