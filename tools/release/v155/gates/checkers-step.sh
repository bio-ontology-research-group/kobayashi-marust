#!/usr/bin/env bash
# Checker step after the five gates (L1: checkers-on suite results recorded).
#   checkers-step.sh <ctl-dir> <km-binary> <out-dir>
# 1. Builds every Lean checker once from the bound snapshot (lake build; the
#    gates delete their native checkers after hashing them).
# 2. lean/run-checker-tests.sh: the 22 CI-skipped checker-bound lib tests and
#    the checker integration tests, serially, against those checkers.
# 3. tools/checkers-on-suite.sh on the default fixture set with the PGO RC
#    binary (modes off, on, ht), then removes the native checkers again.
set -euo pipefail
ctl=$(cd "${1:?ctl dir}" && pwd); km=$(readlink -f "${2:?km binary}"); out=${3:?out dir}
snap=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["snapshot"])' "$ctl/pins.json")
commit=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["commit"])' "$ctl/pins.json")
[ "$(git -C "$snap" rev-parse HEAD)" = "$commit" ] && [ -z "$(git -C "$snap" status --porcelain --untracked-files=no)" ]
mkdir -p "$out"
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH CARGO_TARGET_DIR="$ctl/gate-work/target"
start=$(date +%s)
# `lake build` alone builds only the two library default targets; the
# checkers are `[[lean_exe]]` targets and must be named. The gates delete
# the executables after their audit and leave lake's traces behind, so the
# stale traces of missing executables are removed first.
exes=$(grep -A1 '^\[\[lean_exe\]\]' "$snap/lean/lakefile.toml" | sed -n 's/^name = "\(.*\)"/\1/p')
(cd "$snap/lean/.lake/build/bin" 2>/dev/null && for t in *.trace; do b=${t%.trace}; [ -e "$b" ] || rm -f "$b.trace" "$b.hash"; done) || true
# shellcheck disable=SC2086
(cd "$snap/lean" && LEAN_NUM_THREADS=8 nice lake build $exes) > "$out/lake-build.log" 2>&1
echo "lake_build_s $(( $(date +%s) - start ))" > "$out/timings.txt"
bin="$snap/lean/.lake/build/bin"
(cd "$snap/lean/.lake/build/bin" && sha256sum $(ls | grep -v -E '\.(hash|rsp|trace|json)$')) > "$out/checkers.sha256"
t=$(date +%s)
(cd "$snap/engine" && nice cargo build --release --offline --locked --bin ofn --bin elc --bin kobayashi-marust --bin tableau_cli) > "$out/workers-build.log" 2>&1
"$snap/lean/run-checker-tests.sh" "$bin" > "$out/checker-tests.log" 2>&1 || true
echo "checker_tests_s $(( $(date +%s) - t ))" >> "$out/timings.txt"
grep -c '^test .* ok$' "$out/checker-tests.log" | sed 's/^/checker_tests_ok /' >> "$out/timings.txt"
grep -E '^test .* (FAILED|ignored)' "$out/checker-tests.log" > "$out/checker-tests-not-ok.txt" || true
t=$(date +%s)
"$snap/tools/checkers-on-suite.sh" "$km" "$bin" "$out/checkers-on-suite" > "$out/checkers-on-suite.log" 2>&1
echo "checkers_on_suite_s $(( $(date +%s) - t ))" >> "$out/timings.txt"
python3 - "$out" "$km" "$commit" <<'PY'
import hashlib, json, sys
from pathlib import Path
out, km, commit = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
not_ok = [l for l in (out / 'checker-tests-not-ok.txt').read_text().splitlines() if l.strip()]
r = {'schema': 'km-v155-checker-step-receipt-v1', 'commit': commit, 'km_binary_sha256': H(km),
     'checkers_sha256_list_sha256': H(out / 'checkers.sha256'),
     'checker_tests_log_sha256': H(out / 'checker-tests.log'), 'checker_tests_not_ok': not_ok,
     'suite_summary': str(out / 'checkers-on-suite/summary.md'),
     'suite_summary_sha256': H(out / 'checkers-on-suite/summary.md'),
     'timings': dict(l.split() for l in (out / 'timings.txt').read_text().splitlines()),
     'status': 'passed' if not any('FAILED' in l for l in not_ok) else 'failed'}
(out / 'receipt.json').write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps(r, indent=1))
PY
find "$bin" -maxdepth 1 -type f ! -name '*.hash' ! -name '*.rsp' ! -name '*.trace' ! -name '*.json' -delete
