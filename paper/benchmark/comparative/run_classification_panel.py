"""Measure unchanged original corpus inputs; include every failure outcome."""
import collections
import json
from pathlib import Path
import sys

from measure_classification import measure, digest

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sources = Path(__file__).parent
manifest_path = sources / 'classification-inputs.json'
manifest = json.loads(manifest_path.read_text())
baselines = ['rustdl', 'hermit', 'jfact', 'openllet', 'elk', 'whelk', 'more', 'sequoia']
if len(sys.argv) > 4:
    baselines = sys.argv[4].split(',')
baseline = baselines[task % len(baselines)]
chunk = task // len(baselines)
inputs = manifest['inputs'][chunk * 32:(chunk + 1) * 32]
assert len(inputs) == 32, 'classification chunk missing inputs'
inventory_path = root / (sys.argv[5] if len(sys.argv) > 5 else 'artifact-inventory-53198415.json')
inventory = json.loads(inventory_path.read_text())
out = root / ('classification-' + job)
summary_path = out / 'chunks' / f'{task:03}.json'
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = {'baseline': baseline, 'chunk': chunk, 'manifest_sha256': digest(manifest_path),
           'inventory_sha256': digest(inventory_path), 'runner_sha256': digest(__file__),
           'status': 'running', 'outcomes': []}
def publish():
    temp = summary_path.with_suffix('.part')
    temp.write_text(json.dumps(summary, indent=2) + '\n')
    temp.replace(summary_path)
publish()
for row in inputs:
    record = measure(inventory, baseline, row['path'], row['sha256'], out / baseline / row['ontology'])
    summary['outcomes'].append({'ontology': row['ontology'], 'status': record['status'],
                                'input_admission': row['input_admission']})
    publish()
summary.update(status='measurement_complete_requires_semantic_audit',
               counts=dict(collections.Counter(r['status'] for r in summary['outcomes'])))
publish()
print(json.dumps(summary))
