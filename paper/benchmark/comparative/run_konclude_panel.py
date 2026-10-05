"""Konclude corpus measurement with separately recorded verified OWL/XML input."""
import json
from pathlib import Path
import subprocess
import sys

import tree_watchdog as watchdog
from measure_classification import measure, digest

root, task, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
sources = Path(__file__).parent
manifest = json.loads((sources / 'classification-inputs.json').read_text())
inputs = manifest['inputs'][task * 32:(task + 1) * 32]
assert len(inputs) == 32
inventory = json.loads((root / 'artifact-inventory-53198415.json').read_text())
runtime = next(r for r in inventory['artifacts'] if r['id'] == 'hermit')
assert digest(runtime['path']) == runtime['sha256']
out = root / ('classification-konclude-' + job)
chunk = out / 'chunks' / str(task)
chunk.mkdir(parents=True, exist_ok=False)
classes = chunk / 'classes'
classes.mkdir()
compiler = ['javac', '--release', '11', '-cp', runtime['path'], '-d', str(classes), str(sources / 'ConvertSyntax.java')]
with (chunk / 'compile.stdout').open('wb') as stdout, (chunk / 'compile.stderr').open('wb') as stderr:
    subprocess.run(compiler, stdout=stdout, stderr=stderr, check=True, timeout=60)
converter_hash = digest(classes / 'org/kmbenchmark/ConvertSyntax.class')
summary = {'baseline': 'konclude', 'chunk': task, 'status': 'running', 'outcomes': [],
           'manifest_sha256': digest(sources / 'classification-inputs.json'),
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
        measurement = measure(inventory, 'konclude', source['path'], source['sha256'],
                              out / 'konclude' / source['ontology'], xml, record['runtime_source_sha256'],
                              conversion_receipt=receipt)
        status = measurement['status']
    else:
        status = 'input_' + record['status']
    summary['outcomes'].append({'ontology': source['ontology'], 'status': status,
                                'input_admission': source['input_admission'], 'conversion_status': record['status']})
    publish(chunk / 'summary.json', summary)
summary['status'] = 'measurement_complete_requires_semantic_audit'
publish(chunk / 'summary.json', summary)
print(json.dumps(summary))
