"""Run one frozen baseline under the common classification resource protocol.

This records execution and raw output. A completed process is deliberately not
labelled a correct classification: independent semantic validation is separate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import tree_watchdog as watchdog


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def measure(inventory, baseline, source, source_sha256, output, runtime_source=None,
            runtime_sha256=None, timeout=240, memory_mib=20480, conversion_receipt=None):
    source, output = Path(source).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    runtime_source = Path(runtime_source).resolve() if runtime_source else source
    row = next(r for r in inventory['artifacts'] if r['id'] == baseline)
    record = {'schema': 1, 'baseline': baseline, 'source': str(source), 'source_sha256': source_sha256,
              'runtime_source': str(runtime_source), 'artifact': row['path'], 'artifact_sha256': row['sha256'],
              'runner_sha256': digest(__file__), 'watchdog_sha256': digest(watchdog.__file__),
              'timeout_s': timeout, 'memory_mib': memory_mib, 'cpu_threads': 1,
              'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID'),
              'status': 'preparing', 'semantic_validation': 'pending'}

    def publish():
        tmp = output / 'record.json.part'
        tmp.write_text(json.dumps(record, indent=2) + '\n')
        tmp.replace(output / 'record.json')

    publish()
    try:
        if digest(source) != source_sha256:
            raise ValueError('source hash mismatch')
        if digest(row['path']) != row['sha256']:
            raise ValueError('baseline artifact hash mismatch')
        if runtime_source != source and not runtime_sha256:
            raise ValueError('converted source requires pinned hash and separately verified conversion receipt')
        actual_runtime_hash = digest(runtime_source)
        if actual_runtime_hash != (runtime_sha256 or source_sha256):
            raise ValueError('runtime input hash mismatch')
        record['runtime_source_sha256'] = actual_runtime_hash
        if runtime_source != source:
            if not conversion_receipt:
                raise ValueError('converted input has no semantic round-trip receipt')
            receipt_path = Path(conversion_receipt)
            lines = receipt_path.read_text().splitlines()
            if not lines or lines[-1] != 'Z\tcomplete':
                raise ValueError('incomplete conversion receipt')
            fields = dict(line.split('\t', 2)[1:] for line in lines if line.startswith('M\t'))
            expected = {'source_sha256': source_sha256, 'output_sha256': actual_runtime_hash,
                        'roundtrip_logical_axioms_equal': 'true', 'roundtrip_signature_equal': 'true'}
            if any(fields.get(k) != v for k, v in expected.items()):
                raise ValueError('conversion receipt does not prove source equivalence')
            if baseline == 'konclude' and fields.get('serialization') != 'owlxml':
                raise ValueError('Konclude requires verified OWL/XML serialization')
            record['conversion_receipt_sha256'] = digest(receipt_path)
            record['converter_sha256'] = fields.get('converter_sha256')
        # Sequoia's launcher is only a small script; bind the actual JARs too.
        if baseline == 'sequoia':
            root = Path(row['runtime_root']).resolve()
            for item in row['runtime_files']:
                path = (root / item['path']).resolve()
                if root not in path.parents or digest(path) != item['sha256']:
                    raise ValueError('Sequoia runtime hash mismatch: ' + item['path'])
            record['runtime_manifest_sha256'] = row['runtime_manifest_sha256']
        env = dict(os.environ)
        explicit = {'OMP_NUM_THREADS': '1', 'RAYON_NUM_THREADS': '1', 'KM_THREADS': '1', 'KM_ROUTE': 'auto',
                    'JAVA_OPTS': '-Xms256m -Xmx16g -XX:ActiveProcessorCount=1'}
        env.update(explicit)
        taxonomy = output / 'taxonomy.raw'
        stdout_is_taxonomy = baseline in ['km', 'rustdl']
        java = ['java', '-Xms256m', '-Xmx16g', '-XX:ActiveProcessorCount=1']
        if baseline == 'km':
            command = [row['path'], 'classify', str(runtime_source)]
            fmt = 'km-json'
        elif baseline == 'rustdl':
            command = [row['path'], 'classify', '--json', str(runtime_source)]
            fmt = 'rustdl-json'
        elif baseline == 'konclude':
            if runtime_source == source:
                raise ValueError('Konclude requires a verified OWL/XML conversion')
            lib = Path(row['path']).parent / 'runtime-lib'
            if not lib.is_dir():
                raise ValueError('Konclude runtime libraries missing')
            explicit['LD_LIBRARY_PATH'] = str(lib)
            env['LD_LIBRARY_PATH'] = str(lib)
            command = [row['path'], 'classification', '-w', '1', '-v', '-i', str(runtime_source), '-o', str(taxonomy)]
            fmt = 'owlxml'
        elif baseline == 'sequoia':
            command = [row['path'], '-no-version-check', '-main', 'com.sequoiareasoner.cli.Sequoia',
                       'classify', '--output', str(taxonomy), str(runtime_source)]
            fmt = 'functional'
        elif baseline == 'more':
            command = java + ['-cp', row['path'], 'org.kmbenchmark.FullIriClassifier3', row['factory'],
                              str(runtime_source), str(taxonomy)]
            fmt = 'owlapi-tsv'
        else:
            command = java + ['-jar', row['path'], row['factory'], str(runtime_source), str(taxonomy)]
            fmt = 'owlapi-tsv'
        allowed = os.sched_getaffinity(0)
        cpu = min(allowed)
        record.update(command=command, explicit_environment=explicit, output_format=fmt,
                      cpu_affinity=[cpu], status='running')
        publish()
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        started = time.monotonic()
        def checkpoint(status, peak):
            record.update(status=status, peak_bytes=peak, wall_s=time.monotonic() - started)
            publish()
        watchdog.protect_supervisor()
        measured_command = ['/usr/bin/time', '-f', '%M', '-o', str(output / 'max-rss-kib.txt')] + command
        with (taxonomy if stdout_is_taxonomy else output / 'stdout').open('wb') as stdout, (output / 'stderr').open('wb') as stderr:
            proc = subprocess.Popen(measured_command, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                    env=env, preexec_fn=child)
            result = watchdog.monitor(proc, timeout=timeout, memcap_bytes=memory_mib * 1024**2,
                                      sample_interval=.02, on_trip=checkpoint)
        peak = result.peak_bytes
        for line in (output / 'max-rss-kib.txt').read_text().splitlines():
            if line.isdigit():
                peak = max(peak, int(line) * 1024)
        record.update(status=result.status, exit_code=proc.returncode, wall_s=result.wall_s,
                      peak_bytes=peak, sampled_peak_bytes=result.peak_bytes)
        if record['status'] == 'ok':
            if peak > memory_mib * 1024**2:
                record['status'] = 'memout'
            elif proc.returncode != 0:
                record['status'] = 'process_error'
            elif not taxonomy.is_file() or taxonomy.stat().st_size == 0:
                record['status'] = 'missing_output'
            else:
                record['status'] = 'executed_unvalidated'
        record['files'] = {f.name: {'sha256': digest(f), 'bytes': f.stat().st_size}
                           for f in output.iterdir() if f.is_file() and f.name != 'record.json'}
    except Exception as error:
        record.update(status='adapter_error', error=str(error))
    publish()
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--inventory', type=Path, required=True)
    p.add_argument('--baseline', required=True)
    p.add_argument('--source', type=Path, required=True)
    p.add_argument('--source-sha256', required=True)
    p.add_argument('--runtime-source', type=Path)
    p.add_argument('--runtime-sha256')
    p.add_argument('--conversion-receipt', type=Path)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    record = measure(json.loads(a.inventory.read_text()), a.baseline, a.source, a.source_sha256,
                     a.output, a.runtime_source, a.runtime_sha256, conversion_receipt=a.conversion_receipt)
    print(json.dumps(record))
