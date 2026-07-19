#!/bin/bash
# Build an independent full-IRI oracle for ORE 4669's private negative mirrors.
#
# Submit from a directory containing both Java helpers and
# validate_4669_proxy_oracle.py. Optional environment:
#   RUN_ROOT=/persistent/output/directory
#   CANDIDATE_KM=/path/to/km                 (run it here)
#   CANDIDATE_JSON=/path/to/existing.json    (or compare an existing output)
#   CANDIDATE_ROUTE=ht_bridge
#
# Without either candidate variable the job still builds and cross-validates
# the standalone oracle artifact.
#SBATCH --job-name=km-4669-proxy-oracle
#SBATCH --account=pi-hohndor
#SBATCH --partition=batch
#SBATCH --time=04:00:00
#SBATCH --cpus-per-task=16
#SBATCH --mem=64G
#SBATCH --output=/ibex/scratch/hohndor/km/routing_20260715/4669-proxy-oracle-%j.out

set -euo pipefail

km_root=/ibex/scratch/hohndor/km
source_ontology=$km_root/corpus/ore_ont_4669.owl
run_root=${RUN_ROOT:-$km_root/routing_20260715/4669-proxy-oracle-v2-20260719}
script_dir=${ORACLE_SOURCE_DIR:-${SLURM_SUBMIT_DIR:-$(cd "$(dirname "$0")" && pwd)}}
java=$km_root/bench/jdk8u492-b09/bin/java
javac=$km_root/bench/jdk8u492-b09/bin/javac
owlapi_cp=$km_root/bench/hermit_cp/'*'
konclude=$km_root/Konclude-official
elk=$km_root/bench/reasoners/elk-distribution-cli-0.6.0/elk.jar

classes=$run_root/classes
projected=$run_root/ore_ont_4669-positive-projection.ofn
mapping=$run_root/negative-positive-mapping.tsv
certificate=$run_root/structural-certificate.json
konclude_out=$run_root/konclude-projected.owl
elk_out=$run_root/elk-projected.owl
hermit_cross=$run_root/hermit-base-to-negative.tsv.gz
hermit_cross_summary=$run_root/hermit-base-to-negative.summary.json
expected=$run_root/original-public-taxonomy.oracle.tsv.gz
report=$run_root/oracle-comparison.json

/usr/bin/mkdir -p "$run_root" "$classes"
/usr/bin/sha256sum \
    "$source_ontology" \
    "$script_dir/ProxyProjection4669.java" \
    "$script_dir/ProjectedDisjointOracle4669.java" \
    "$script_dir/validate_4669_proxy_oracle.py" \
    "$konclude" "$elk" > "$run_root/input-manifest.sha256"

"$javac" -cp "$owlapi_cp" -d "$classes" \
    "$script_dir/ProxyProjection4669.java" \
    "$script_dir/ProjectedDisjointOracle4669.java"

/usr/bin/time -v -o "$run_root/projector.time.txt" \
    "$java" -Xmx24g -cp "$classes:$owlapi_cp" ProxyProjection4669 \
    "$source_ontology" "$projected" "$mapping" "$certificate" \
    > "$run_root/projector.stdout.json" \
    2> "$run_root/projector.stderr.log"

# The projection is a conservative extension and contains no negative mirror
# names. For N_i == not P_i, HermiT's complete disjoint-class query returns
# exactly the named base classes A for which A <= N_i in the source ontology.
/usr/bin/timeout -k 10 5400 /usr/bin/time -v -o "$run_root/hermit-disjoint.time.txt" \
    "$java" -Xmx56g -cp "$classes:$owlapi_cp" ProjectedDisjointOracle4669 \
    "$projected" "$mapping" "$hermit_cross" "$hermit_cross_summary" \
    > "$run_root/hermit-disjoint.stdout.json" \
    2> "$run_root/hermit-disjoint.stderr.log"

export LD_LIBRARY_PATH="$km_root:${LD_LIBRARY_PATH:-}"
/usr/bin/timeout -k 10 1800 /usr/bin/time -v -o "$run_root/konclude.time.txt" \
    "$konclude" classification -w 16 -v -i "$projected" -o "$konclude_out" \
    > "$run_root/konclude.stdout.log" \
    2> "$run_root/konclude.stderr.log"

/usr/bin/timeout -k 10 1800 /usr/bin/time -v -o "$run_root/elk.time.txt" \
    "$java" -Xmx56g -jar "$elk" -c -q -i "$projected" -o "$elk_out" \
    > "$run_root/elk.stdout.log" \
    2> "$run_root/elk.stderr.log"

candidate_args=()
if [[ -n ${CANDIDATE_JSON:-} ]]; then
    candidate_args=(--candidate-km "$CANDIDATE_JSON")
elif [[ -n ${CANDIDATE_KM:-} ]]; then
    candidate_json=$run_root/km-candidate.json
    candidate_route=${CANDIDATE_ROUTE:-ht_bridge}
    /usr/bin/timeout -k 10 600 /usr/bin/time -v -o "$run_root/km-candidate.time.txt" \
        /usr/bin/env KM_ROUTE="$candidate_route" "$CANDIDATE_KM" classify "$source_ontology" \
        > "$candidate_json" 2> "$run_root/km-candidate.stderr.log"
    /usr/bin/sha256sum "$CANDIDATE_KM" > "$run_root/km-candidate-binary.sha256"
    candidate_args=(--candidate-km "$candidate_json")
fi

/usr/bin/time -v -o "$run_root/checker.time.txt" \
    /usr/bin/python3 "$script_dir/validate_4669_proxy_oracle.py" \
    --source "$source_ontology" \
    --projected "$projected" \
    --mapping "$mapping" \
    --certificate "$certificate" \
    --konclude-taxonomy "$konclude_out" \
    --hermit-disjoint "$hermit_cross" \
    --hermit-disjoint-summary "$hermit_cross_summary" \
    --elk-taxonomy "$elk_out" \
    "${candidate_args[@]}" \
    --expected-tsv "$expected" \
    --report "$report" \
    > "$run_root/checker.stdout.json" \
    2> "$run_root/checker.stderr.log"

/usr/bin/sha256sum \
    "$projected" "$mapping" "$certificate" \
    "$hermit_cross" "$hermit_cross_summary" \
    "$konclude_out" "$elk_out" "$expected" "$report" \
    > "$run_root/output-manifest.sha256"
/usr/bin/cat "$report"
