#!/usr/bin/env bash
#
# run_oracle.sh <ontology-file>
#
# Validation oracle: classify the given ontology with the HermiT reasoner
# (via the OWL API) and print a JSON object on stdout describing
#   - consistency,
#   - all entailed atomic subsumptions A SubClassOf B over named classes,
#   - the named classes that are unsatisfiable (equivalent to owl:Nothing).
#
# Re-usable on any OWL ontology the OWL API can parse (.ofn, .owl, .ttl, ...).
#
set -euo pipefail

ORACLE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# HermiT is an *external* dependency (not vendored here). Point HERMIT_DIR at a
# checkout/build of HermiT (e.g. the OWL API HermiT distribution); defaults to a
# sibling `hermit-reasoner/` if present. Reference oracle outputs are committed in
# oracle/results/, so the cross-check is reproducible without rebuilding HermiT.
HERMIT_DIR="${HERMIT_DIR:-$ORACLE_DIR/../hermit-reasoner}"

export JAVA_HOME="${JAVA_HOME:-/usr/lib/jvm/java-21-openjdk-amd64}"

if [ "$#" -ne 1 ]; then
    echo "Usage: $(basename "$0") <ontology-file>" >&2
    exit 2
fi
ONT="$1"

# Locate the HermiT jar (built with: mvn -DskipTests -Dmaven.javadoc.skip=true package).
HERMIT_JAR="$(ls "$HERMIT_DIR"/target/org.semanticweb.hermit-*.jar 2>/dev/null \
              | grep -v sources | head -n1 || true)"
if [ -z "$HERMIT_JAR" ]; then
    echo "HermiT jar not found in $HERMIT_DIR/target." >&2
    echo "Build it first:  (cd $HERMIT_DIR && JAVA_HOME=$JAVA_HOME mvn -q -DskipTests -Dmaven.javadoc.skip=true -Dgpg.skip=true package)" >&2
    exit 1
fi

# Cache the dependency classpath (OWL API etc.) next to this script.
CP_FILE="$ORACLE_DIR/.classpath.txt"
if [ ! -s "$CP_FILE" ]; then
    ( cd "$HERMIT_DIR" && JAVA_HOME="$JAVA_HOME" mvn -q dependency:build-classpath \
        -Dmdep.outputFile="$CP_FILE" >/dev/null )
fi
DEP_CP="$(cat "$CP_FILE")"

FULL_CP="$ORACLE_DIR:$HERMIT_JAR:$DEP_CP"

# Compile Oracle.java once (recompile if source is newer than class).
if [ ! -f "$ORACLE_DIR/Oracle.class" ] || [ "$ORACLE_DIR/Oracle.java" -nt "$ORACLE_DIR/Oracle.class" ]; then
    "$JAVA_HOME/bin/javac" -cp "$FULL_CP" -d "$ORACLE_DIR" "$ORACLE_DIR/Oracle.java" >&2
fi

# Run. Silence SLF4J/HermiT noise on stderr so stdout stays clean JSON.
exec "$JAVA_HOME/bin/java" -cp "$FULL_CP" Oracle "$ONT"
