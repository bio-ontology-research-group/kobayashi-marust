#!/usr/bin/env bash
# Checkers-on suite (docs/CHECKERS-ON.md section 3).
#
#   tools/checkers-on-suite.sh KM_BINARY CHECKER_DIR OUT_DIR [INPUTS.tsv ...]
#
# Runs `km classify` on every input in modes off, on (KM_LEAN_CHECKERS) and
# ht (plus KM_LEAN_CHECKERS_HT=1), four runs at a time, one thread each, 60 s
# each, then writes OUT_DIR/summary.md and OUT_DIR/per-input.tsv. Without
# INPUTS.tsv files it builds the default input set: every ontology under
# engine/tests/fixtures. SUITE_MODES, SUITE_JOBS, SUITE_TIMEOUT and
# SUITE_GOLD (colon-separated HermiT answer directories) override the
# defaults. Re-running resumes: finished (input, mode) pairs are kept.
set -euo pipefail
repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
km=${1:?usage: tools/checkers-on-suite.sh KM CHECKER_DIR OUT_DIR [INPUTS.tsv ...]}
checkers=${2:?checker directory}
out=${3:?output directory}
shift 3
mkdir -p "$out"
km=$(cd "$(dirname "$km")" && pwd)/$(basename "$km")
checkers=$(cd "$checkers" && pwd)
if (($# == 0)); then
    find "$repo_root/engine/tests/fixtures" -type f \
        \( -name '*.ofn' -o -name '*.owl' -o -name '*.owx' -o -name '*.ttl' \) |
        sort | awk '{ print "fixture\t" $0 }' > "$out/inputs-fixtures.tsv"
    set -- "$out/inputs-fixtures.tsv"
fi
gold_args=()
IFS=: read -r -a gold_dirs <<< "${SUITE_GOLD:-}"
for dir in "${gold_dirs[@]}"; do
    [[ -n "$dir" ]] && gold_args+=(--gold "$dir")
done
{
    echo "km $(sha256sum "$km" | cut -d' ' -f1) $km"
    (cd "$checkers" && sha256sum $(ls | grep -v -E '\.(hash|rsp|trace|json)$'))
} > "$out/binaries.sha256"
python3 -I "$repo_root/tools/checkers_on_suite.py" run \
    --km "$km" --checkers "$checkers" --out "$out" \
    --jobs "${SUITE_JOBS:-4}" --timeout "${SUITE_TIMEOUT:-60}" \
    --modes "${SUITE_MODES:-off,on,ht}" "${gold_args[@]}" "$@"
python3 -I "$repo_root/tools/checkers_on_suite.py" summarize "$out" > /dev/null
echo "summary: $out/summary.md"
