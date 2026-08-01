#!/bin/bash
# Build the ORE 4669 full-taxonomy oracle using the certified empty
# base-to-negative cross region. Konclude classifies both the positive
# projection and a conservative extension naming every conjunction operand.
#SBATCH --job-name=km-4669-zero-cross
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=01:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/4669-zero-cross-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
source_ontology=$km_root/corpus/ore_ont_4669.owl
run_root=${RUN_ROOT:?set RUN_ROOT to a persistent scratch directory}
script_dir=${ORACLE_SOURCE_DIR:?set ORACLE_SOURCE_DIR to the staged helper directory}
java=$km_root/bench/jdk8u492-b09/bin/java
javac=$km_root/bench/jdk8u492-b09/bin/javac
owlapi_cp=$km_root/bench/hermit_cp/'*'
konclude=$km_root/Konclude-official
elk=$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar

classes=$run_root/classes
projected=$run_root/ore_ont_4669-positive-projection.ofn
mapping=$run_root/negative-positive-mapping.tsv
certificate=$run_root/structural-certificate.json
zero_cross=$script_dir/4669-zero-cross-candidates.tsv
zero_certificate=$script_dir/4669-zero-cross-certificate.json
konclude_out=$run_root/konclude-projected.owl
elk_out=$run_root/elk-projected.owl
augmented=$run_root/ore_ont_4669-positive-projection-augmented.ofn
augmented_konclude_out=$run_root/konclude-augmented.owl
expected=$run_root/original-public-taxonomy.oracle.tsv.gz
report=$run_root/oracle-comparison.json

/usr/bin/mkdir -p "$run_root" "$classes"
/usr/bin/sha256sum \
    "$source_ontology" \
    "$script_dir/ProxyProjection4669.java" \
    "$script_dir/ElkCandidatePairs4669.java" \
    "$script_dir/validate_4669_proxy_oracle.py" \
    "$zero_cross" "$zero_certificate" \
    "$konclude" "$elk" > "$run_root/input-manifest.sha256"

"$javac" -cp "$owlapi_cp" -d "$classes" \
    "$script_dir/ProxyProjection4669.java" \
    "$script_dir/ElkCandidatePairs4669.java"

/usr/bin/time -v -o "$run_root/projector.time.txt" \
    "$java" -Xmx24g -cp "$classes:$owlapi_cp" ProxyProjection4669 \
    "$source_ontology" "$projected" "$mapping" "$certificate" \
    > "$run_root/projector.stdout.json" \
    2> "$run_root/projector.stderr.log"

export LD_LIBRARY_PATH="$km_root:${LD_LIBRARY_PATH:-}"
/usr/bin/timeout -k 10 1800 /usr/bin/time -v -o "$run_root/konclude.time.txt" \
    "$konclude" classification -w 16 -v -i "$projected" -o "$konclude_out" \
    > "$run_root/konclude.stdout.log" \
    2> "$run_root/konclude.stderr.log"

/usr/bin/timeout -k 10 1800 /usr/bin/time -v -o "$run_root/elk.time.txt" \
    "$java" -Xmx56g -jar "$elk" -c -q -i "$projected" -o "$elk_out" \
    > "$run_root/elk.stdout.log" \
    2> "$run_root/elk.stderr.log"

/usr/bin/time -v -o "$run_root/augment.time.txt" \
    "$java" -Xmx24g -cp "$classes:$owlapi_cp" ElkCandidatePairs4669 \
    "$projected" "$run_root/unused-candidates.tsv" "$run_root/unused-summary.json" \
    "--emit-augmented=$augmented" \
    > "$run_root/augment.stdout.log" \
    2> "$run_root/augment.stderr.log"

/usr/bin/timeout -k 10 1800 /usr/bin/time -v \
    -o "$run_root/konclude-augmented.time.txt" \
    "$konclude" classification -w 16 -v -i "$augmented" \
    -o "$augmented_konclude_out" \
    > "$run_root/konclude-augmented.stdout.log" \
    2> "$run_root/konclude-augmented.stderr.log"

/usr/bin/time -v -o "$run_root/checker.time.txt" \
    /usr/bin/python3 "$script_dir/validate_4669_proxy_oracle.py" \
    --source "$source_ontology" \
    --projected "$projected" \
    --mapping "$mapping" \
    --certificate "$certificate" \
    --konclude-taxonomy "$konclude_out" \
    --zero-cross-certificate "$zero_certificate" \
    --zero-cross-candidates "$zero_cross" \
    --augmented-projection "$augmented" \
    --augmented-konclude-taxonomy "$augmented_konclude_out" \
    --elk-taxonomy "$elk_out" \
    --expected-tsv "$expected" \
    --report "$report" \
    > "$run_root/checker.stdout.json" \
    2> "$run_root/checker.stderr.log"

/usr/bin/sha256sum \
    "$projected" "$mapping" "$certificate" \
    "$zero_cross" "$zero_certificate" \
    "$konclude_out" "$elk_out" "$augmented" "$augmented_konclude_out" \
    "$expected" "$report" \
    > "$run_root/output-manifest.sha256"
/usr/bin/cat "$report"
