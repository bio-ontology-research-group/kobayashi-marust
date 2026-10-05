"""Resolve only admitted-input clause-order differences in a completed frontend audit."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from check_empty_iri_frontend import digest
import tree_watchdog as watchdog

parser = argparse.ArgumentParser()
parser.add_argument('--frontend-job', required=True)
args = parser.parse_args()
assert args.frontend_job.isdigit()
root = Path(__file__).resolve().parent
manifest_path = root / 'full-candidate-inputs.json'
manifest = json.loads(manifest_path.read_text())
original = root / ('empty-iri-frontend-' + args.frontend_job)
rows, chunk_hashes = [], {}
for task in range(60):
    path = original / 'chunks' / (str(task) + '.json')
    chunk = json.loads(path.read_text())
    assert chunk['status'] == 'complete'
    assert chunk['manifest_sha256'] == digest(manifest_path)
    assert chunk['artifact_manifest_sha256'] == digest(root / 'empty-iri-frontend-artifacts.json')
    assert chunk['checker_sha256'] == digest(root / 'check_empty_iri_frontend.py')
    chunk_hashes[str(task)] = digest(path)
    rows.extend(chunk['outcomes'])
assert [r['ontology'] for r in rows] == [r['ontology'] for r in manifest['inputs']]
assert [r['source_sha256'] for r in rows] == [r['sha256'] for r in manifest['inputs']]
selected = [r for r, source in zip(rows, manifest['inputs'])
            if not r['passed'] and source['input_admission'] == 'checks_passed']
output = root / ('empty-iri-clause-order-' + os.environ['SLURM_JOB_ID'])
output.mkdir(parents=True, exist_ok=True)
summary_path = output / 'summary.json'
assert not summary_path.exists()
summary = dict(status='running', frontend_job=args.frontend_job, source_chunks=chunk_hashes,
               manifest_sha256=digest(manifest_path), runner_sha256=digest(__file__),
               checker_sha256=digest(root / 'compare_frontend_clause_multiset.py'),
               selected=[r['ontology'] for r in selected], outcomes=[],
               scope='Only failed admitted-input frontend comparisons; invalid-input refusals require their own audit.')
def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)
watchdog.protect_supervisor()
publish()
for row in selected:
    name = row['ontology']
    receipt = output / (name + '.json')
    command = [sys.executable, str(root / 'compare_frontend_clause_multiset.py'),
               '--directory', str(original / name), '--ontology', name, '--output', str(receipt)]
    with (output / (name + '.stdout')).open('wb') as out, (output / (name + '.stderr')).open('wb') as err:
        process = subprocess.Popen(command, stdout=out, stderr=err,
                                   stdin=subprocess.DEVNULL, preexec_fn=watchdog.child_preexec)
        execution = watchdog.monitor(process, timeout=600, memcap_bytes=20480 * 1024**2)
    result = dict(ontology=name, source_sha256=row['source_sha256'], execution_status=execution.status,
                  returncode=process.returncode, passed=execution.status == 'ok' and process.returncode == 0)
    if result['passed']:
        proof = json.loads(receipt.read_text())
        assert proof['passed'] and proof['ontology'] == name
        result.update(receipt_sha256=digest(receipt), renaming=proof['renaming'])
    summary['outcomes'].append(result)
    publish()
summary['status'] = 'complete'
summary['all_selected_preserved'] = all(r['passed'] for r in summary['outcomes'])
publish()
