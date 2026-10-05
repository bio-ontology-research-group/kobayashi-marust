"""Exercise measured generation and independent verification on shared modules."""
import json
from pathlib import Path
import subprocess
import sys

from measure_justification_java import measure, digest

root, baseline, job = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
inventory = {r['id']: r for r in json.loads((root / 'artifact-inventory-53198415.json').read_text())['artifacts']}
generator, verifier = inventory[baseline], inventory['jfact' if baseline == 'hermit' else 'hermit']
out = root / ('measured-justification-pilot-' + job) / baseline
out.mkdir(parents=True, exist_ok=False)
sources = Path(__file__).parent
for label, row, name in [('generator', generator, 'EntailmentExplanation.java'), ('verifier', verifier, 'VerifyJustification.java')]:
    assert digest(row['path']) == row['sha256']
    if label == 'generator' and baseline in ['km', 'rustdl']:
        continue
    classes = out / label
    classes.mkdir()
    command = ['javac', '--release', '11', '-cp', row['path'], '-d', str(classes), str(sources / name)]
    with (out / (label + '.compile.stdout')).open('wb') as stdout, (out / (label + '.compile.stderr')).open('wb') as stderr:
        subprocess.run(command, stdout=stdout, stderr=stderr, check=True, timeout=60)
shared = root / 'java-justification-pilot-53198928/hermit'
report = {'generator': baseline, 'verifier': verifier['id'], 'cases': [], 'status': 'running'}
for name, sup in [('chain', 'urn:v145:C'), ('existential', 'urn:v145:D')]:
    source, module = shared / (name + '.ofn'), shared / (name + '.module.ofn')
    record = measure(generator, verifier, None if baseline in ['km', 'rustdl'] else out / 'generator', out / 'verifier', source, digest(source),
                     module, digest(module), 'urn:v145:A', sup, out / name, timeout=40)
    report['cases'].append({'case': name, 'status': record['status'], 'error': record.get('error')})
report['status'] = 'passed' if all(r['status'] == 'independently_verified' for r in report['cases']) else 'failed'
(out / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
