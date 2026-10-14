"""Check repaired public output against an explicit entailment or saved oracle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('--binary', required=True, type=Path)
p.add_argument('--source', required=True, type=Path)
p.add_argument('--baseline', type=Path)
p.add_argument('--output', required=True, type=Path)
a = p.parse_args()
env = {key: value for key, value in os.environ.items() if not key.startswith('KM_')}
env.update(KM_HT_NATIVE_FULL='1', KM_HT_DDB='1')
started = time.monotonic()
r = subprocess.run([str(a.binary.resolve()), 'classify', '--route', 'ht_bridge', str(a.source.resolve())],
                   env=env, capture_output=True, text=True, timeout=60)
wall = time.monotonic()-started
assert r.returncode == 0, (r.returncode, r.stderr[-1000:])
answer = json.loads(r.stdout)
expected = json.loads(a.baseline.read_text()) if a.baseline else {
    'consistent': True, 'subsumptions': [['urn:test:A', 'urn:test:C']],
    'unsatisfiable': [], 'dropped': 0}
def signature(result):
    return (result['consistent'], set(map(tuple, result['subsumptions'])),
            set(result['unsatisfiable']), result['dropped'])
assert signature(answer) == signature(expected), 'public answer mismatch'
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
receipt = dict(diagnostic_only=True, binary_sha256=digest(a.binary),
               source_sha256=digest(a.source), baseline_sha256=digest(a.baseline) if a.baseline else None,
               wall_s=wall, identical_answer=True, pairs=len(answer['subsumptions']),
               output_sha256=hashlib.sha256(r.stdout.encode()).hexdigest(),
               flags={'KM_HT_NATIVE_FULL':'1', 'KM_HT_DDB':'1'},
               scope='One local diagnostic run, not a release performance measurement.')
a.output.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
