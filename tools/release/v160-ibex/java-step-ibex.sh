#!/usr/bin/env bash
# Java gate from the tag: Maven package (runs the Protégé/OWLAPI test suite)
# in the bound snapshot with the PGO RC binary; writes <ctl>/java-receipt.json
# in the v1.5.4 java_receipt shape.
#   java-step.sh <ctl-dir> <km-binary>
set -euo pipefail
ctl=$(cd "${1:?ctl dir}" && pwd); km=$(readlink -f "${2:?km binary}")
: # Ibex edition: Maven from the module system (maven/3.9.1, java/24.0.2)
MVN=$(command -v mvn)
snap=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["snapshot"])' "$ctl/pins.json")
commit=$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["commit"])' "$ctl/pins.json")
[ "$(git -C "$snap" rev-parse HEAD)" = "$commit" ]
mkdir -p "$ctl/../logs"
log=$ctl/../logs/mvn-package-from-tag.log
start=$(date +%s)
(cd "$snap/protege" && nice "$MVN" -o -B -Dkm.bin="$km" package) > "$log" 2>&1
end=$(date +%s)
[ -z "$(git -C "$snap" status --porcelain --untracked-files=no)" ]
python3 - "$ctl" "$snap" "$commit" "$km" "$MVN" "$log" "$((end - start))" <<'PY'
import glob, hashlib, json, re, subprocess, sys
from pathlib import Path
ctl, snap, commit, km, mvn, log, wall = sys.argv[1:]
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
text = Path(log).read_text(errors='replace')
m = re.findall(r'Tests run: (\d+), Failures: (\d+), Errors: (\d+), Skipped: (\d+)\s*$', text, re.M)
assert m, 'no Maven test summary'
run, fail, err, skip = map(int, m[-1])
jars = [j for j in glob.glob(f'{snap}/protege/target/kobayashi-marust-protege-*.jar') if 'sources' not in j and 'javadoc' not in j]
assert len(jars) == 1, jars
r = {'schema': 'km-v155-java-receipt-v1', 'source_commit': commit, 'execution_source': f'{snap}/protege',
     'command': [mvn, '-o', '-B', f'-Dkm.bin={km}', 'package'],
     'km_binary_for_tests': {'path': km, 'sha256': H(km), 'note': 'the PGO release-candidate binary (wrapper-linked)'},
     'jdk': subprocess.run(['java', '-version'], capture_output=True, text=True).stderr.splitlines()[0],
     'maven': subprocess.run([mvn, '-v'], capture_output=True, text=True).stdout.splitlines()[0],
     'tests': {'run': run, 'failures': fail, 'errors': err, 'skipped': skip},
     'package_log': {'path': log, 'sha256': H(log)}, 'jar': jars[0], 'jar_sha256': H(jars[0]), 'wall_s': int(wall),
     'status': 'passed' if fail == 0 and err == 0 and 'BUILD SUCCESS' in text else 'failed'}
Path(ctl, 'java-receipt.json').write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps({k: r[k] for k in ('tests', 'jar_sha256', 'status', 'wall_s')}))
PY
