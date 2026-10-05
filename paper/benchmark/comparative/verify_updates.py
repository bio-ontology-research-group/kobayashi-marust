"""Audit every serialized revision against its intended original-source view."""
import json
from pathlib import Path
import subprocess
import sys

import tree_watchdog as watchdog
from measure_classification import digest

root, index, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
row = json.loads((root / 'workload-selection.json').read_text())['selected'][index]
runtime = next(r for r in json.loads((root / 'artifact-inventory-53198415.json').read_text())['artifacts'] if r['id'] == 'hermit')
prepared = root / 'prepared-updates-53198993' / row['ontology']
out = root / ('verified-updates-' + job) / row['ontology']
out.mkdir(parents=True, exist_ok=False)
record = {'ontology': row['ontology'], 'source_sha256': row['sha256'], 'status': 'running',
          'runner_sha256': digest(__file__), 'verifier_sha256': digest(Path(__file__).parent / 'VerifyUpdates.java')}
def publish():
    temporary = out / 'record.json.part'
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    temporary.replace(out / 'record.json')
publish()
try:
    assert digest(row['path']) == row['sha256'], 'source changed'
    assert digest(runtime['path']) == runtime['sha256'], 'runtime changed'
    receipt = json.loads((prepared / 'receipt.json').read_text())
    assert receipt['status'] == 'prepared', 'preparation failed'
    for i in range(5):
        name = f'{i:03}.ofn'
        assert digest(prepared / 'revisions' / name) == receipt['files'][name], 'revision changed'
    record['preparation_receipt_sha256'] = digest(prepared / 'receipt.json')
    classes = out / 'classes'
    classes.mkdir()
    with (out / 'compile.stdout').open('wb') as stdout, (out / 'compile.stderr').open('wb') as stderr:
        subprocess.run(['javac', '--release', '11', '-cp', runtime['path'], '-d', str(classes),
                        str(Path(__file__).parent / 'VerifyUpdates.java')], stdout=stdout, stderr=stderr, check=True, timeout=60)
    command = ['java', '-Xmx16g', '-XX:ActiveProcessorCount=1', '-cp', str(classes) + ':' + runtime['path'],
               'org.kmbenchmark.VerifyUpdates', row['path'], str(prepared / 'revisions'), str(out / 'verification.tsv')]
    record['command'] = command
    watchdog.protect_supervisor()
    def checkpoint(status, peak):
        record.update(status=status, peak_bytes=peak)
        publish()
    with (out / 'stdout').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
        process = subprocess.Popen(command, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                   preexec_fn=watchdog.child_preexec)
        result = watchdog.monitor(process, timeout=900, memcap_bytes=20480 * 1024**2, on_trip=checkpoint)
    record.update(status=result.status, exit_code=process.returncode, wall_s=result.wall_s, peak_bytes=result.peak_bytes)
    if result.status == 'ok':
        record['status'] = 'verified' if process.returncode == 0 else 'verification_failed'
    if (out / 'verification.tsv').exists():
        record['verification'] = (out / 'verification.tsv').read_text()
except Exception as error:
    record.update(status='adapter_error', error=str(error))
publish()
print(json.dumps(record))
