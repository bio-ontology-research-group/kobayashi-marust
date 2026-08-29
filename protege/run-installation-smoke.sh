#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
    echo "usage: $0 PROTEGE_HOME PLUGIN_JAR KM_BINARY" >&2
    exit 64
fi

protege_home=$(realpath "$1")
plugin_jar=$(realpath "$2")
km_binary=$(realpath "$3")
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

for required in \
    "$protege_home/run.sh" \
    "$protege_home/bundles/protege-launcher.jar" \
    "$plugin_jar" \
    "$km_binary"; do
    if [[ ! -e $required ]]; then
        echo "missing installation-smoke input: $required" >&2
        exit 66
    fi
done

run_dir=$(mktemp -d "$repo/.work/protege-install-smoke.XXXXXX")
classes="$run_dir/classes"
home="$run_dir/home"
log="$run_dir/protege.log"
mkdir -p "$classes" "$home"

javac --release 11 -proc:none \
    -cp "$protege_home/bundles/*:$plugin_jar" \
    -d "$classes" \
    "$repo/protege/smoke/src/org/bioontology/kobayashimarust/smoke/ProtegeInstallationSmoke.java"
jar cfm "$run_dir/zz-km-installation-smoke.jar" \
    "$repo/protege/smoke/MANIFEST.MF" \
    -C "$classes" .

cp "$plugin_jar" "$protege_home/plugins/"
cp "$run_dir/zz-km-installation-smoke.jar" "$protege_home/plugins/"

set +e
(
    cd "$protege_home"
    timeout 120s env \
        HOME="$home" \
        JAVA_HOME="${JAVA_HOME:-/usr}" \
        KM_BIN="$km_binary" \
        CMD_OPTIONS='-Djava.awt.headless=true' \
        ./run.sh
) >"$log" 2>&1
status=$?
set -e

if ! grep -q '^KM_PROTEGE_INSTALLATION_SMOKE_OK$' "$log"; then
    echo "Protégé installation smoke failed (launcher status $status): $log" >&2
    tail -n 120 "$log" >&2
    exit 1
fi
if grep -Eq \
    "Unable to resolve org\.bioontology\.kobayashi-marust|Error starting .*plugins/kobayashi-marust-protege" \
    "$log"; then
    echo "KM bundle reported an OSGi start error: $log" >&2
    exit 1
fi

echo "Protégé installation smoke passed: $log"
