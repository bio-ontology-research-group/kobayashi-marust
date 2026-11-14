#!/bin/sh
# HermiT's object property rows for one ontology, in the row convention of
# docs/PROPERTIES.md: run_hermit_props.sh <ontology> [--entail]
#
# PROTEGE points at a Protege 5.6 install (its HermiT plugin and OWL API
# bundle); WORK is a writable directory for the extracted jars and classes.
set -eu
PROTEGE=${PROTEGE:?set PROTEGE to a Protege-5.6.x directory}
WORK=${WORK:?set WORK to a writable scratch directory}
HERE=$(cd "$(dirname "$0")" && pwd)
if [ ! -f "$WORK/classes/HermitProps.class" ]; then
  mkdir -p "$WORK/lib" "$WORK/classes"
  (cd "$WORK/lib" && unzip -o -q "$PROTEGE/plugins/org.semanticweb.hermit-1.4.3.456.jar" '*.jar' \
    && unzip -o -q "$PROTEGE/bundles/owlapi-osgidistribution.jar" 'lib/*.jar')
fi
CP="$PROTEGE/plugins/org.semanticweb.hermit-1.4.3.456.jar:$PROTEGE/bundles/owlapi-osgidistribution.jar"
for jar in "$WORK"/lib/*.jar "$WORK"/lib/lib/*.jar; do CP="$CP:$jar"; done
CP="$CP:$PROTEGE/bundles/slf4j-api.jar:$PROTEGE/bundles/guava.jar:$PROTEGE/bundles/org.apache.servicemix.bundles.javax-inject.jar"
if [ ! -f "$WORK/classes/HermitProps.class" ]; then
  javac -proc:none -cp "$CP" -d "$WORK/classes" "$HERE/HermitProps.java"
fi
exec java -Xmx16g -cp "$WORK/classes:$CP" HermitProps "$@"
