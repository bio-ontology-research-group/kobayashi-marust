#!/usr/bin/env bash
# Run the HermiT/KM differential on a list of ontologies, one at a time.
#
#   run_parity.sh <list file or ontology paths...> <out dir>
#
# A single argument ending in .txt or .list is a file with one ontology path per line
# (lines starting with # are ignored); otherwise every argument but the last
# is an ontology path. Environment:
#   KM_BIN        km executable (required)
#   MVN           Maven launcher (default: mvn)
#   PARITY_TMP    scratch/temp directory, never /tmp (required)
#   PARITY_OPTS   extra ParityRun options, e.g. "--timeout 60 --sample 100"
#   SKIP_BUILD=1  do not rebuild the plugin classes or this module
# Output: <out dir>/<ontology name>.json plus <name>.workers/ (raw worker logs).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
: "${KM_BIN:?set KM_BIN to the km executable}"
: "${PARITY_TMP:?set PARITY_TMP to a scratch directory outside /tmp}"
case "$PARITY_TMP" in /tmp|/tmp/*) echo "PARITY_TMP must not be under /tmp" >&2; exit 2;; esac
mkdir -p "$PARITY_TMP"
export TMPDIR="$PARITY_TMP" KM_THREADS=1
export JAVA_TOOL_OPTIONS="-Djava.io.tmpdir=$PARITY_TMP"
MVN="${MVN:-mvn}"

if [ "$#" -lt 2 ]; then echo "usage: $0 <ontology list | paths...> <out dir>" >&2; exit 2; fi
out="${@: -1}"
args=("${@:1:$#-1}")
if [ "${#args[@]}" -eq 1 ] && [[ "${args[0]}" == *.txt || "${args[0]}" == *.list ]]; then
  mapfile -t onts < <(grep -v '^\s*#' "${args[0]}" | grep .)
else
  onts=("${args[@]}")
fi
mkdir -p "$out"

if [ "${SKIP_BUILD:-0}" != 1 ]; then
  (cd "$here/../protege" && "$MVN" -o -q compile)
  (cd "$here" && "$MVN" -o -q compile dependency:build-classpath -Dmdep.outputFile=target/classpath.txt)
fi
cp="$here/target/classes:$(cat "$here/target/classpath.txt"):$here/../protege/target/protege5/classes"

for o in "${onts[@]}"; do
  name="$(basename "$o")"; name="${name%.*}"
  echo "== $name" >&2
  java -Xmx2g -Djava.io.tmpdir="$PARITY_TMP" -Dkm.bin="$KM_BIN" -cp "$cp" \
    org.bioontology.kobayashimarust.parity.ParityRun ${PARITY_OPTS:-} "$o" "$out/$name.json" \
    || echo "ParityRun failed on $o" >&2
done
