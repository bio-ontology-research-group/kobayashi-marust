#!/usr/bin/env bash
# Preserve raw stdout/exit status for the harness and retain a typed refusal.
set -uo pipefail
binary="${KM140_BIN:?missing candidate}"
input="$1"
output="${HARNESS_OUT_DIR:?missing output directory}"
mkdir -p "$output"
name=$(basename "${input%.*}")
"$binary" classify --route auto "$input" \
    > >(tee "$output/$name.json") \
    2> >(tee "$output/$name.stderr" >&2)
result=$?
wait
python="${KM_REPORT_PYTHON:-/usr/bin/python3.9}"
"$python" - "$output" "$name" "$result" <<'PY'
import hashlib,json,pathlib,sys
root,name,code=sys.argv[1:]
root=pathlib.Path(root);code=int(code)
raw=(root/(name+'.stderr')).read_bytes()
lines=raw.decode(errors='replace').splitlines()
invalid=next((line for line in lines if line.startswith('invalid OWL 2 DL input')),None)
status=('invalid_input' if code==2 and invalid else
        'unsupported' if code==3 else 'ok' if code==0 else 'execution_error')
(root/(name+'.execution.json')).write_text(json.dumps({
    'ontology':name,'status':status,'exit_code':code,
    'diagnostic':invalid if status=='invalid_input' else None,
    'stderr_sha256':hashlib.sha256(raw).hexdigest(),
    'stdout_sha256':hashlib.sha256((root/(name+'.json')).read_bytes()).hexdigest(),
})+'\n')
PY
report_result=$?
if [ "$report_result" -ne 0 ]; then exit "$report_result"; fi
exit "$result"
