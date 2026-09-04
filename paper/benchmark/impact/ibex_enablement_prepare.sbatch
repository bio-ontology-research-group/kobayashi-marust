#!/bin/bash
#SBATCH --account=pi-hohndor
#SBATCH --partition=debug
#SBATCH --time=00:20:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=12G
#SBATCH --job-name=km-enable-prepare

set -euo pipefail
: "${IMPACT_ROOT:?set IMPACT_ROOT}"

benchmark=/ibex/scratch/hohndor/km/paper-benchmark-20260830
staged="$IMPACT_ROOT/staged"
classes="$IMPACT_ROOT/classes"
inputs="$IMPACT_ROOT/inputs"
receipts="$IMPACT_ROOT/receipts"
mkdir -p "$classes" "$inputs" "$receipts" "$IMPACT_ROOT/logs"

projection_source="$staged/MakeELProjection.java"
elk_jar="$benchmark/runtimes/classifier-elk.jar"
galen=/ibex/scratch/hohndor/km/corpus/ore_ont_9724.owl
control="$staged/product-configuration-control.ofn"
conflict="$staged/product-configuration-conflict.ofn"

test "$(sha256sum "$projection_source" | awk '{print $1}')" = 12954e6072d29cb76e7a227675cfdb8258f07adcb4d10d317fcdfc80ece0d35a
test "$(sha256sum "$elk_jar" | awk '{print $1}')" = 7ffc442f2966667a488479a748502276136445c8e44ffd9e8498873a401cb3d4
test "$(sha256sum "$galen" | awk '{print $1}')" = 00c80e07aa57578c168d15a1755b62fde41c53dd69a2f04cc5d88c888c8baf19
test "$(sha256sum "$control" | awk '{print $1}')" = baad9238c8bcbf1519d3b006299334a52cf489a5f4b57292de32ffec69e0d2f3
test "$(sha256sum "$conflict" | awk '{print $1}')" = a92e020a6957504fc4ee1d206389288e65a8c8637d874d42aaacc31899e0fde6

rm -rf "$classes/org"
/usr/bin/javac -cp "$elk_jar" -d "$classes" "$projection_source"
class_file="$classes/org/kmbenchmark/MakeELProjection.class"
test -s "$class_file"

project() {
  local source=$1 stem=$2
  rm -f "$inputs/$stem.ofn" "$receipts/$stem.projection.tsv"
  /usr/bin/time -v -o "$receipts/$stem.projection.time" \
    /usr/bin/java -Xmx8g -cp "$classes:$elk_jar" \
    org.kmbenchmark.MakeELProjection "$source" "$inputs/$stem.ofn" \
    "$receipts/$stem.projection.tsv"
  test -s "$inputs/$stem.ofn"
  grep -Fxq $'P\tOWL2EL\ttrue\t0' "$receipts/$stem.projection.tsv"
  grep -Fxq $'Z\tcomplete' "$receipts/$stem.projection.tsv"
}

project "$control" product-control-el
project "$conflict" product-conflict-el
project "$galen" galen-ore9724-el

{
  printf 'schema\t1\n'
  printf 'status\tcomplete\n'
  printf 'slurm_job_id\t%s\n' "$SLURM_JOB_ID"
  printf 'host\t%s\n' "$(hostname)"
  printf 'projection_source_sha256\t%s\n' "$(sha256sum "$projection_source" | awk '{print $1}')"
  printf 'projection_class_sha256\t%s\n' "$(sha256sum "$class_file" | awk '{print $1}')"
  printf 'owlapi_elk_jar_sha256\t%s\n' "$(sha256sum "$elk_jar" | awk '{print $1}')"
  for stem in product-control-el product-conflict-el galen-ore9724-el; do
    printf '%s_sha256\t%s\n' "$stem" "$(sha256sum "$inputs/$stem.ofn" | awk '{print $1}')"
    printf '%s_receipt_sha256\t%s\n' "$stem" "$(sha256sum "$receipts/$stem.projection.tsv" | awk '{print $1}')"
  done
  printf 'terminal_marker\tPREPARATION_COMPLETE\n'
} > "$receipts/preparation.receipt.tsv"
