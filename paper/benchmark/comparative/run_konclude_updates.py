"""Konclude fresh-process updates with separately verified OWL/XML revisions."""
import json
from pathlib import Path
import subprocess
import sys

import tree_watchdog as watchdog
from measure_classification import measure, digest

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sources = Path(__file__).parent
source = json.loads((root / 'workload-selection.json').read_text())['selected'][task]
out = root / ('konclude-updates-' + job) / source['ontology']
try:
    prepared = root / ('prepared-updates-' + sys.argv[4]) / source['ontology']
    receipt = json.loads((prepared / 'receipt.json').read_text())
    assert receipt['status'] == 'prepared', 'update preparation failed'
    assert receipt['source_sha256'] == source['sha256'], 'source hash mismatch'
    verification = prepared / 'revisions/verification.tsv'
    assert digest(verification) == receipt['files']['verification.tsv'], 'preservation receipt changed'
    assert verification.read_text().endswith('status\tpassed\n'), 'source preservation failed'
    inputs = [{'ontology': f'{index:03}', 'path': str(prepared / 'revisions' / f'{index:03}.ofn'),
               'sha256': receipt['files'][f'{index:03}.ofn'], 'input_admission': 'verified source revision'}
              for index in range(5)]
except Exception as error:
    out.mkdir(parents=True, exist_ok=False)
    (out / 'summary.json').write_text(json.dumps({
        'baseline': 'konclude', 'ontology': source['ontology'],
        'status': 'preparation_failed', 'error': str(error),
        'source_sha256': source['sha256'], 'runner_sha256': digest(__file__)
    }, indent=2) + '\n')
    raise SystemExit(0)
inventory = json.loads((root / 'artifact-inventory-53198415.json').read_text())
runtime = next(r for r in inventory['artifacts'] if r['id'] == 'hermit')
assert digest(runtime['path']) == runtime['sha256']
out = root / ('konclude-updates-' + job) / source['ontology']
chunk = out / 'chunks' / str(task)
chunk.mkdir(parents=True, exist_ok=False)
classes = chunk / 'classes'
classes.mkdir()
compiler = ['javac', '--release', '11', '-cp', runtime['path'], '-d', str(classes), str(sources / 'ConvertSyntax.java')]
with (chunk / 'compile.stdout').open('wb') as stdout, (chunk / 'compile.stderr').open('wb') as stderr:
    subprocess.run(compiler, stdout=stdout, stderr=stderr, check=True, timeout=60)
converter_hash = digest(classes / 'org/kmbenchmark/ConvertSyntax.class')
summary = {'baseline': 'konclude', 'chunk': task, 'status': 'running', 'outcomes': [],
           'preparation_receipt_sha256': digest(prepared / 'receipt.json'),
           'mode': 'fresh process per revision',
           'runner_sha256': digest(__file__), 'converter_source_sha256': digest(sources / 'ConvertSyntax.java'),
           'converter_class_sha256': converter_hash, 'converter_runtime_sha256': runtime['sha256']}
def publish(path, value):
    temporary = path.with_suffix('.part')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)
watchdog.protect_supervisor()
for source in inputs:
    converted = out / 'conversion' / source['ontology']
    converted.mkdir(parents=True, exist_ok=False)
    xml = converted / 'input.owlxml'
    receipt = converted / 'roundtrip.tsv'
    record = {'ontology': source['ontology'], 'source_sha256': source['sha256'], 'input_admission': source['input_admission'],
              'status': 'preparing', 'timeout_s': 600, 'memory_mib': 20480}
    publish(converted / 'record.json', record)
    try:
        assert digest(source['path']) == source['sha256'], 'source hash mismatch'
        command = ['java', '-Xmx16g', '-XX:ActiveProcessorCount=1', '-Dkm.converter.sha256=' + converter_hash,
                   '-cp', str(classes) + ':' + runtime['path'], 'org.kmbenchmark.ConvertSyntax',
                   source['path'], str(xml), str(receipt), 'owlxml']
        record['command'] = command
        def checkpoint(status, peak):
            record.update(status=status, peak_bytes=peak)
            publish(converted / 'record.json', record)
        with (converted / 'stdout').open('wb') as stdout, (converted / 'stderr').open('wb') as stderr:
            process = subprocess.Popen(command, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                       preexec_fn=watchdog.child_preexec)
            result = watchdog.monitor(process, timeout=600, memcap_bytes=20480 * 1024**2, on_trip=checkpoint)
        record.update(status=result.status, exit_code=process.returncode, wall_s=result.wall_s, peak_bytes=result.peak_bytes)
        if result.status == 'ok' and process.returncode == 0 and receipt.exists() and xml.exists():
            record.update(status='converted', runtime_source_sha256=digest(xml), receipt_sha256=digest(receipt))
        elif result.status == 'ok':
            record['status'] = 'conversion_error'
    except Exception as error:
        record.update(status='conversion_adapter_error', error=str(error))
    publish(converted / 'record.json', record)
    if record['status'] == 'converted':
        statuses = []
        for repetition in range(3):
            measurement = measure(inventory, 'konclude', source['path'], source['sha256'],
                                  out / f'repetition-{repetition}' / source['ontology'], xml,
                                  record['runtime_source_sha256'], conversion_receipt=receipt)
            statuses.append(measurement['status'])
        status = statuses
    else:
        status = 'input_' + record['status']
    summary['outcomes'].append({'ontology': source['ontology'], 'status': status,
                                'input_admission': source['input_admission'], 'conversion_status': record['status']})
    publish(chunk / 'summary.json', summary)
summary['status'] = 'measurement_complete_requires_semantic_audit'
publish(chunk / 'summary.json', summary)
print(json.dumps(summary))
