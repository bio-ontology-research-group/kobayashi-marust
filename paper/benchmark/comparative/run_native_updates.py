"""Fresh-process update comparisons for pinned native CLI adapters."""
import json
from pathlib import Path
import sys

from measure_classification import measure, digest

root, task, job, preparation_job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
baselines = ['rustdl', 'more', 'sequoia']
source = json.loads((root / 'workload-selection.json').read_text())['selected'][task // len(baselines)]
baseline = baselines[task % len(baselines)]
inventory = json.loads((root / 'artifact-inventory-53198415.json').read_text())
out = root / ('native-updates-' + job) / source['ontology'] / baseline
out.mkdir(parents=True, exist_ok=False)
summary = {'baseline': baseline, 'ontology': source['ontology'], 'status': 'preparing',
           'mode': 'fresh process per revision', 'retained_session': 'not exposed by this pinned CLI adapter',
           'source_sha256': source['sha256'], 'runner_sha256': digest(__file__), 'cases': []}
def publish():
    temporary = out / 'summary.json.part'
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(out / 'summary.json')
publish()
try:
    prepared = root / ('prepared-updates-' + preparation_job) / source['ontology']
    receipt = json.loads((prepared / 'receipt.json').read_text())
    assert receipt['status'] == 'prepared', 'preparation failed'
    assert receipt['source_sha256'] == source['sha256'], 'source hash mismatch'
    verification = prepared / 'revisions/verification.tsv'
    assert digest(verification) == receipt['files']['verification.tsv'], 'preservation receipt changed'
    assert verification.read_text().endswith('status\tpassed\n'), 'source preservation failed'
    summary['preparation_receipt_sha256'] = digest(prepared / 'receipt.json')
    summary['status'] = 'running'
    for repetition in range(3):
        for revision in range(5):
            name = f'{revision:03}.ofn'
            record = measure(inventory, baseline, prepared / 'revisions' / name, receipt['files'][name],
                             out / f'repetition-{repetition}' / f'{revision:03}')
            summary['cases'].append({'repetition': repetition, 'revision': revision, 'status': record['status']})
            publish()
    summary['status'] = 'measurement_complete_requires_semantic_audit'
except Exception as error:
    summary.update(status='preparation_or_adapter_error', error=str(error))
publish()
print(json.dumps(summary))
