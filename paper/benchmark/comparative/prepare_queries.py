"""Prepare source-bound HermiT queries; reference failures stay in the panel."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys

import tree_watchdog as watchdog


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    root, index, job = Path(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    row = json.loads((root / 'workload-selection.json').read_text())['selected'][index]
    art = next(r for r in json.loads((root / 'artifact-inventory-53198415.json').read_text())['artifacts']
               if r['id'] == 'hermit')
    out = root / ('prepared-queries-' + job) / row['ontology']
    out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).parent / 'PrepareQueries.java'
    receipt = {'ontology': row['ontology'], 'source': row['path'], 'source_sha256': row['sha256'],
               'reference_runtime_sha256': art['sha256'], 'generator_sha256': digest(source),
               'runner_sha256': digest(__file__), 'host': os.uname().nodename,
               'slurm_job_id': os.getenv('SLURM_JOB_ID'), 'stages': [], 'status': 'running'}

    def publish():
        tmp = out / 'receipt.json.part'
        tmp.write_text(json.dumps(receipt, indent=2) + '\n')
        tmp.replace(out / 'receipt.json')

    def run(command, name, timeout):
        stage = {'name': name, 'command': command, 'timeout_s': timeout, 'memory_mib': 20480,
                 'status': 'running'}
        receipt['stages'].append(stage)
        publish()
        def checkpoint(status, peak):
            stage.update(status=status, peak_bytes=peak)
            receipt['status'] = name + '_' + status
            publish()
        with (out / (name + '.stdout')).open('wb') as stdout, (out / (name + '.stderr')).open('wb') as stderr:
            process = subprocess.Popen(command, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                       preexec_fn=watchdog.child_preexec)
            result = watchdog.monitor(process, timeout=timeout, memcap_bytes=20480 * 1024**2,
                                      sample_interval=.02, on_trip=checkpoint)
        stage.update(status=result.status, exit_code=process.returncode,
                     wall_s=result.wall_s, peak_bytes=result.peak_bytes)
        if result.status == 'ok' and process.returncode != 0:
            stage['status'] = 'error'
        publish()
        if stage['status'] != 'ok':
            raise RuntimeError(name + '_' + stage['status'])

    watchdog.protect_supervisor()
    try:
        assert digest(row['path']) == row['sha256'], 'source hash changed'
        assert digest(art['path']) == art['sha256'], 'reference artifact hash changed'
        classes = out / 'classes'
        classes.mkdir()
        run(['javac', '--release', '11', '-cp', art['path'], '-d', str(classes), str(source)], 'compile', 60)
        java = ['java', '-Xmx16g', '-XX:ActiveProcessorCount=1']
        taxonomy = out / 'reference.tsv'
        if len(sys.argv) > 4:
            previous = root / ('prepared-queries-' + sys.argv[4]) / row['ontology']
            old = json.loads((previous / 'receipt.json').read_text())
            assert old['source_sha256'] == row['sha256'], 'reference source binding changed'
            assert old['reference_runtime_sha256'] == art['sha256'], 'reference runtime changed'
            reference = next(s for s in old['stages'] if s['name'] == 'reference')
            receipt['reused_reference_receipt_sha256'] = digest(previous / 'receipt.json')
            if reference['status'] != 'ok' or reference['exit_code'] != 0:
                raise RuntimeError('frozen_reference_failure: ' + reference['status'])
            prior_taxonomy = previous / 'reference.tsv'
            if 'reference_taxonomy_sha256' in old:
                assert digest(prior_taxonomy) == old['reference_taxonomy_sha256'], 'reference output changed'
            shutil.copyfile(prior_taxonomy, taxonomy)
            receipt['reference_taxonomy_sha256'] = digest(taxonomy)
            receipt['reused_reference_stage'] = reference
        else:
            run(java + ['-jar', art['path'], art['factory'], row['path'], str(taxonomy)], 'reference', 240)
        run(java + ['-cp', str(classes) + ':' + art['path'], 'org.kmbenchmark.PrepareQueries',
                    row['path'], str(taxonomy), str(out / 'queries')], 'modules', 600)
        assert (out / 'queries/COMPLETE').is_file(), 'missing module completion marker'
        receipt['reference_taxonomy_sha256'] = digest(taxonomy)
        receipt['files'] = {f.name: {'sha256': digest(f), 'bytes': f.stat().st_size}
                            for f in (out / 'queries').iterdir() if f.is_file()}
        receipt['status'] = 'prepared'
    except Exception as error:
        receipt.update(status='query_preparation_failed', error=str(error))
    publish()
    print(json.dumps({'ontology': row['ontology'], 'status': receipt['status'], 'error': receipt.get('error')}))


if __name__ == '__main__':
    main()
