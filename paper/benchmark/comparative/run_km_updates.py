"""Full paired cold/retained KM source-update panel; preserve actual reuse receipts."""
import json
import os
from pathlib import Path
import subprocess
import sys

from measure_classification import measure as cold, digest
from measure_retained_km import measure as retained

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
preparation_job = sys.argv[4]
selection = json.loads((root / 'workload-selection.json').read_text())['selected']
baselines = ['km']
source = selection[task // len(baselines)]
baseline = baselines[task % len(baselines)]
inventory = json.loads((root / (sys.argv[5] if len(sys.argv)>5 else 'artifact-inventory-v145-candidate.json')).read_text())
row = next(r for r in inventory['artifacts'] if r['id'] == baseline)
out = root / ('km-updates-' + job) / source['ontology'] / baseline
out.mkdir(parents=True, exist_ok=False)
summary = {'ontology': source['ontology'], 'baseline': baseline, 'source_sha256': source['sha256'],
           'status': 'preparing', 'repetitions': [], 'runner_sha256': digest(__file__),
           'slurm_job_id': os.getenv('SLURM_JOB_ID')}
def publish():
    temp = out / 'summary.json.part'
    temp.write_text(json.dumps(summary, indent=2) + '\n')
    temp.replace(out / 'summary.json')
publish()
try:
    prepared = root / ('prepared-updates-' + preparation_job) / source['ontology']
    receipt = json.loads((prepared / 'receipt.json').read_text())
    assert receipt['status'] == 'prepared', 'update preparation failed'
    assert receipt['source_sha256'] == source['sha256'], 'prepared source hash mismatch'
    verification = prepared / 'revisions/verification.tsv'
    assert digest(verification) == receipt['files']['verification.tsv'], 'verification receipt changed'
    assert verification.read_text().endswith('status\tpassed\n'), 'source-preservation audit failed'
    summary['preparation_receipt_sha256'] = digest(prepared / 'receipt.json')
    revisions = [{'path': str(prepared / 'revisions' / f'{i:03}.ofn'),
                  'sha256': receipt['files'][f'{i:03}.ofn']} for i in range(5)]
    assert digest(row['path']) == row['sha256'], 'runtime hash mismatch'
    summary['status'] = 'running'
    for repetition in range(3):
        repeat = out / f'repetition-{repetition}'
        repeat.mkdir()
        # Alternate order, balanced by ontology and baseline, to expose cache effects.
        order = ['cold', 'retained'] if (task + repetition) % 2 == 0 else ['retained', 'cold']
        result = {'repetition': repetition, 'order': order, 'outcomes': {}}
        summary['repetitions'].append(result)
        publish()
        for mode in order:
            if mode == 'retained':
                record = retained(row, revisions, repeat / 'retained')
                result['outcomes'][mode] = record['status']
            else:
                result['outcomes'][mode] = []
                for index, revision in enumerate(revisions):
                    record = cold(inventory, baseline, revision['path'], revision['sha256'],
                                  repeat / 'cold' / f'{index:03}')
                    result['outcomes'][mode].append(record['status'])
                    publish()
            publish()
    summary['status'] = 'measurement_complete_requires_semantic_audit'
except Exception as error:
    summary.update(status='preparation_or_adapter_error', error=str(error))
publish()
print(json.dumps(summary))
