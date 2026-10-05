"""Frozen-corpus frontend preservation audit; never a performance benchmark."""
import json
import os
from pathlib import Path
import subprocess
import sys

from check_empty_iri_frontend import digest
import tree_watchdog as watchdog

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'full-candidate-inputs.json').read_text())
artifacts = json.loads((root / 'empty-iri-frontend-artifacts.json').read_text())
for artifact in artifacts.values():
    assert digest(artifact['path']) == artifact['sha256']
task = int(os.environ['SLURM_ARRAY_TASK_ID'])
rows = manifest['inputs'][task * 32:(task + 1) * 32]
assert len(manifest['inputs']) == 1920 and len(rows) == 32
output = root / ('empty-iri-frontend-' + os.environ['SLURM_ARRAY_JOB_ID'])
chunk = output / 'chunks' / (str(task) + '.json')
chunk.parent.mkdir(parents=True, exist_ok=True)
assert not chunk.exists(), 'Do not overwrite an earlier audit'
summary = dict(status='running', manifest_sha256=digest(root / 'full-candidate-inputs.json'),
               artifact_manifest_sha256=digest(root / 'empty-iri-frontend-artifacts.json'),
               runner_sha256=digest(__file__), checker_sha256=digest(root / 'check_empty_iri_frontend.py'),
               scope='All 1920 frozen inputs, including invalid inputs; frontend preservation only.',
               outcomes=[])
def publish():
    partial = chunk.with_suffix('.part')
    partial.write_text(json.dumps(summary, indent=2) + '\n')
    partial.replace(chunk)
watchdog.protect_supervisor()
publish()
for row in rows:
    destination = output / row['ontology']
    destination.mkdir(parents=True, exist_ok=True)
    result = dict(ontology=row['ontology'], source_sha256=row['sha256'], passed=False)
    try:
        assert digest(row['path']) == row['sha256']
        command = [sys.executable, str(root / 'check_empty_iri_frontend.py'),
                   '--old', artifacts['old']['path'], '--new', artifacts['new']['path'],
                   '--source', row['path'], '--output', str(destination), '--timeout', '240']
        with (destination / 'stdout').open('wb') as out, (destination / 'stderr').open('wb') as err:
            process = subprocess.Popen(command, stdout=out, stderr=err,
                                       stdin=subprocess.DEVNULL, preexec_fn=watchdog.child_preexec)
            execution = watchdog.monitor(process, timeout=600, memcap_bytes=20480 * 1024**2)
        result.update(execution_status=execution.status, returncode=process.returncode)
        if execution.status == 'ok' and process.returncode == 0:
            receipt = json.loads((destination / 'receipt.json').read_text())
            assert len(receipt['rows']) == 1
            proof = receipt['rows'][0]
            assert proof['source_sha256'] == row['sha256']
            assert proof['equal_after_source_bound_renaming']
            result.update(passed=True, byte_identical=proof['byte_identical'], renaming=proof['renaming'],
                          receipt_sha256=digest(destination / 'receipt.json'))
            # Retain hashes and proof receipts, not two copies of the entire clause corpus.
            for path in destination.glob(row['ontology'] + '-*.json'):
                path.unlink()
        else:
            result['stderr_sha256'] = digest(destination / 'stderr')
    except Exception as error:
        result['error'] = str(error)
    summary['outcomes'].append(result)
    publish()
summary['status'] = 'complete'
publish()
