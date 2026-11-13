#!/usr/bin/env bash
# Installs the packaged KM plugin and a one-shot consumer bundle into an
# unpacked Protégé distribution, starts Protégé headless, and checks that the
# consumer classifies, updates and explains through the installed plugin.
#
# With KM_BINARY, Protégé runs with KM_BIN set to it, so the plugin must use
# that executable. Without KM_BINARY, the script unsets KM_BIN, removes every
# km from PATH, and the plugin must unpack and run its bundled executable.
# The script then checks which executable the plugin used.
#
# The work directory defaults to <repo>/.work; set KM_SMOKE_WORK_DIR to change it.
set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "usage: $0 PROTEGE_HOME PLUGIN_JAR [KM_BINARY]" >&2
    exit 64
fi

protege_home=$(realpath "$1")
plugin_jar=$(realpath "$2")
km_binary=
if [[ $# -eq 3 ]]; then
    km_binary=$(realpath "$3")
fi
repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
work_dir=${KM_SMOKE_WORK_DIR:-$repo/.work}

for required in \
    "$protege_home/run.sh" \
    "$protege_home/bundles/protege-launcher.jar" \
    "$plugin_jar" \
    ${km_binary:+"$km_binary"}; do
    if [[ ! -e $required ]]; then
        echo "missing installation-smoke input: $required" >&2
        exit 66
    fi
done

if [[ -z $km_binary ]] && ! unzip -l "$plugin_jar" native/SHA256SUMS >/dev/null 2>&1; then
    echo "no KM_BINARY given and $plugin_jar bundles no km executable" >&2
    exit 66
fi

mkdir -p "$work_dir"
run_dir=$(mktemp -d "$work_dir/protege-install-smoke.XXXXXX")
classes="$run_dir/classes"
home="$run_dir/home"
log="$run_dir/protege.log"
mkdir -p "$classes" "$home" "$run_dir/tmp"

# The OWL API bundle nests its own dependencies; OWL API 5 types refer to
# some of them (for example commons-rdf), so javac needs them too.
mkdir -p "$run_dir/owlapi-lib"
unzip -q -j -o "$protege_home/bundles/owlapi-osgidistribution.jar" 'lib/*.jar' \
    -d "$run_dir/owlapi-lib" 2>/dev/null || true

javac --release 11 -proc:none \
    -cp "$protege_home/bundles/*:$run_dir/owlapi-lib/*:$plugin_jar" \
    -d "$classes" \
    "$repo/protege/smoke/src/org/bioontology/kobayashimarust/smoke/ProtegeInstallationSmoke.java"
jar cfm "$run_dir/zz-km-installation-smoke.jar" \
    "$repo/protege/smoke/MANIFEST.MF" \
    -C "$classes" .

# Replace any KM plugin from an earlier run; two KM bundles must not coexist.
rm -f "$protege_home"/plugins/kobayashi-marust-protege*.jar \
    "$protege_home/plugins/zz-km-installation-smoke.jar"
cp "$plugin_jar" "$protege_home/plugins/"
cp "$run_dir/zz-km-installation-smoke.jar" "$protege_home/plugins/"

# Build the PATH for Protégé. Without KM_BINARY, drop every PATH entry that
# holds a km executable, so only the bundled one can satisfy the plugin.
protege_path=$PATH
if [[ -z $km_binary ]]; then
    protege_path=
    IFS=: read -r -a entries <<<"$PATH"
    for entry in "${entries[@]}"; do
        if [[ -n $entry && ! -x $entry/km ]]; then
            protege_path=${protege_path:+$protege_path:}$entry
        fi
    done
    if PATH=$protege_path command -v km >/dev/null 2>&1; then
        echo "km is still on the smoke PATH: $(PATH=$protege_path command -v km)" >&2
        exit 1
    fi
fi

launch=(env -u KM_BIN -u XDG_CACHE_HOME
    HOME="$home"
    PATH="$protege_path"
    JAVA_HOME="${JAVA_HOME:-/usr}"
    # Java takes user.home from the password database, not from HOME, so
    # set it too: the plugin cache, Protégé preferences and temporary files
    # stay in the run directory.
    CMD_OPTIONS="-Djava.awt.headless=true -Duser.home=$home -Djava.io.tmpdir=$run_dir/tmp")
if [[ -n $km_binary ]]; then
    launch+=(KM_BIN="$km_binary")
fi

set +e
(
    cd "$protege_home"
    timeout 120s "${launch[@]}" ./run.sh
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

# HOME is private to this run, so the cache holds only what this run unpacked.
cache="$home/.cache/kobayashi-marust/protege"
case "$(uname -s)" in
    Darwin) cache="$home/Library/Caches/kobayashi-marust/protege" ;;
esac
unpacked=$(find "$cache" -type f -name km 2>/dev/null | head -n 1 || true)
if [[ -n $km_binary ]]; then
    if [[ -n $unpacked ]]; then
        echo "KM_BIN was set, but the plugin unpacked its bundled km: $unpacked" >&2
        exit 1
    fi
    echo "Protégé installation smoke passed with KM_BIN=$km_binary: $log"
else
    if [[ -z $unpacked || ! -x $unpacked ]]; then
        echo "the plugin did not unpack an executable km under $cache" >&2
        exit 1
    fi
    expected=$(unzip -p "$plugin_jar" native/SHA256SUMS |
        awk -v name="$(basename "$(dirname "$unpacked")")/km" '$2 == name { print $1 }' || true)
    if command -v sha256sum >/dev/null 2>&1; then
        actual=$(sha256sum "$unpacked" | awk '{ print $1 }')
    else
        actual=$(shasum -a 256 "$unpacked" | awk '{ print $1 }')
    fi
    if [[ -z $expected || $expected != "$actual" ]]; then
        echo "unpacked km $unpacked does not match native/SHA256SUMS" >&2
        exit 1
    fi
    echo "Protégé installation smoke passed with the bundled km ($unpacked): $log"
fi
