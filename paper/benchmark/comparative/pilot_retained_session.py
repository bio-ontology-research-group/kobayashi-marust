"""Check the measured session adapter against the audited fresh Java pilot."""
import json
from pathlib import Path
import subprocess
import sys

from measure_retained_java import measure, digest

root, baseline, job = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
row = next(r for r in json.loads((root / 'artifact-inventory-53198415.json').read_text())['artifacts']
           if r['id'] == baseline)
assert digest(row['path']) == row['sha256']
out = root / ('retained-session-pilot-' + job) / baseline
out.mkdir(parents=True, exist_ok=False)
classes = out / 'classes'
classes.mkdir()
sources = Path(__file__).parent
command = ['javac', '--release', '11', '-cp', row['path'], '-d', str(classes),
           str(sources / 'FullIriClassifier.java'), str(sources / 'IncrementalClassifier.java')]
with (out / 'compile.stdout').open('wb') as stdout, (out / 'compile.stderr').open('wb') as stderr:
    subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=60)
previous = root / 'java-incremental-pilot-53198499' / baseline
revisions = [{'path': str(previous / f'{i:03}.ofn'), 'sha256': digest(previous / f'{i:03}.ofn')} for i in range(5)]
record = measure(row, revisions, classes, out / 'measurement', timeout=40)
audit = {'baseline': baseline, 'record_status': record['status'], 'status': 'failed', 'revisions': [],
         'sources': {name: digest(sources / name) for name in ['FullIriClassifier.java', 'IncrementalClassifier.java']}}
if record['status'] == 'executed_unvalidated':
    for i in range(5):
        actual = out / 'measurement/session' / f'{i:03}.taxonomy.tsv'
        expected = previous / f'fresh-{i}.tsv'
        audit['revisions'].append({'revision': i, 'fresh_sha256': digest(expected),
                                  'measured_sha256': digest(actual), 'byte_identical': actual.read_bytes() == expected.read_bytes()})
    if all(r['byte_identical'] for r in audit['revisions']):
        audit['status'] = 'passed'
(out / 'audit.json').write_text(json.dumps(audit, indent=2) + '\n')
print(json.dumps(audit))
