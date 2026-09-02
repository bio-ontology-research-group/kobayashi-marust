#!/usr/bin/env bash
# Fail closed before spending a Slurm allocation on a KM deployment.
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: $0 KM_BINARY [EXPECTED_SHA256]" >&2
  exit 2
fi

binary=$(realpath "$1")
expected=${2:-}
[[ -x "$binary" ]] || {
  echo "deployment preflight: binary is missing or not executable: $binary" >&2
  exit 2
}

actual=$(sha256sum "$binary" | cut -d' ' -f1)
if [[ -n "$expected" && "$actual" != "$expected" ]]; then
  echo "deployment preflight: checksum mismatch: expected=$expected actual=$actual" >&2
  exit 2
fi

# This invocation catches an incompatible dynamic loader or GLIBC before the
# benchmark harness mistakes a near-zero-RSS startup failure for a reasoner run.
routes=$($binary routes)
[[ -n "$routes" ]] || {
  echo "deployment preflight: route inventory is empty" >&2
  exit 2
}

tmp_root=${SLURM_TMPDIR:-${TMPDIR:-/tmp}}
smoke=$(mktemp "$tmp_root/km-deployment-smoke.XXXXXX.owl")
output=$(mktemp "$tmp_root/km-deployment-smoke.XXXXXX.json")
trap 'rm -f "$smoke" "$output"' EXIT
printf '%s\n' \
  'Prefix(:=<urn:km:deployment-smoke#>)' \
  'Ontology(' \
  ' Declaration(Class(:A))' \
  ' Declaration(Class(:B))' \
  ' SubClassOf(:A :B)' \
  ')' > "$smoke"

KM_ROUTE=auto "$binary" classify "$smoke" > "$output"
python3 - "$output" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    result = json.load(stream)
assert isinstance(result.get("subsumptions"), list)
assert isinstance(result.get("unsatisfiable"), list)
assert any(pair in ((":A", ":B"), [":A", ":B"])
           or (pair[0].endswith("#A") and pair[1].endswith("#B"))
           for pair in result["subsumptions"]), result
PY

echo "KM_DEPLOYMENT_OK binary_sha256=$actual"
