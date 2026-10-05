"""Generate one explanation from a frozen module and verify it independently."""
import json
import os
from pathlib import Path
import subprocess
import sys
import shutil

import tree_watchdog as watchdog
from measure_classification import digest
from native_justification import support as native_support


def measure(generator, verifier, generator_classes, verifier_classes, source, source_hash,
            module, module_hash, sub, sup, output, timeout=240, memory_mib=20480, consistency_certificate=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    record = {'generator': generator['id'], 'verifier': verifier['id'],
              'source_sha256': source_hash, 'module_sha256': module_hash,
              'query': [sub, sup], 'status': 'preparing', 'stages': [],
              'runner_sha256': digest(__file__), 'watchdog_sha256': digest(watchdog.__file__),
              'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID')}
    def publish():
        temporary = output / 'record.json.part'
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        temporary.replace(output / 'record.json')
    publish()
    def run(command, name):
        cpu = min(os.sched_getaffinity(0))
        stage = {'name': name, 'command': command, 'timeout_s': timeout, 'memory_mib': memory_mib,
                 'cpu_affinity': [cpu], 'status': 'running'}
        record['stages'].append(stage)
        publish()
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        def checkpoint(status, peak):
            stage.update(status=status, peak_bytes=peak)
            record['status'] = name + '_' + status
            publish()
        measured = ['/usr/bin/time', '-f', '%M', '-o', str(output / (name + '.max-rss-kib'))] + command
        with (output / (name + '.stdout')).open('wb') as stdout, (output / (name + '.stderr')).open('wb') as stderr:
            process = subprocess.Popen(measured, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                       env=dict(os.environ, KM_THREADS='1', RAYON_NUM_THREADS='1', OMP_NUM_THREADS='1'),
                                       preexec_fn=child)
            result = watchdog.monitor(process, timeout=timeout, memcap_bytes=memory_mib * 1024**2,
                                      on_trip=checkpoint)
        peak = result.peak_bytes
        rss = output / (name + '.max-rss-kib')
        if rss.exists():
            for line in rss.read_text().splitlines():
                if line.isdigit():
                    peak = max(peak, int(line) * 1024)
        status = result.status
        if status == 'ok':
            status = 'memout' if peak > memory_mib * 1024**2 else 'error' if process.returncode else 'executed'
        stage.update(status=status, wall_s=result.wall_s, peak_bytes=peak, exit_code=process.returncode)
        publish()
        return status == 'executed'
    try:
        assert generator['id'] != verifier['id'], 'verification must use a different reasoner'
        for row in [generator, verifier]:
            assert digest(row['path']) == row['sha256'], 'runtime hash mismatch'
        assert digest(source) == source_hash, 'source hash mismatch'
        assert digest(module) == module_hash, 'module hash mismatch'
        record['artifacts'] = {r['id']: r['sha256'] for r in [generator, verifier]}
        record['compiled_classes'] = {
            label: {str(p.relative_to(Path(classes))): digest(p) for p in Path(classes).rglob('*.class')}
            for label, classes in [('generator', generator_classes), ('verifier', verifier_classes)] if classes is not None}
        watchdog.protect_supervisor()
        java = ['java', '-Xms256m', '-Xmx16g', '-XX:ActiveProcessorCount=1']
        explanation = output / 'explanation.tsv'
        native = generator['id'] in ['km', 'rustdl']
        external = generator['id'] in ['konclude', 'sequoia', 'more']
        if external:
            configuration = {'generator': generator, 'owlapi_runtime': verifier,
                             'module': str(module), 'module_sha256': module_hash,
                             'classes': str(generator_classes), 'sub': sub, 'sup': sup,
                             'output': str(output / 'external'),
                             'consistency_certificate': consistency_certificate}
            config_path = output / 'external-config.json'
            config_path.write_text(json.dumps(configuration, indent=2) + '\n')
            command = [sys.executable, str(Path(__file__).with_name('external_justification.py')), str(config_path)]
        elif native:
            command = [generator['path'], 'explain' if generator['id'] == 'km' else 'justify']
            if generator['id'] == 'rustdl':
                command.append('--json')
            else:
                # Input bytes bound the number of source axioms without reparsing.
                # Resource limits govern this benchmark, not interactive CLI caps.
                command += ['--max-axioms', str(Path(module).stat().st_size),
                            '--max-source-bytes', str(Path(module).stat().st_size),
                            '--max-checks', str(2**63 - 1), '--max-justifications', '1']
            command += [str(module), 'subclass', sub, sup]
        else:
            command = java + ['-cp', str(generator_classes) + ':' + generator['path'],
                              'org.kmbenchmark.EntailmentExplanation', generator['factory'], str(module),
                              sub, sup, str(output / 'module.ofn'), str(explanation), 'frozen-module']
            if generator['id'] == 'whelk':
                command.append('hierarchy-deletion')
        if not run(command, 'generation'):
            record['status'] = 'generation_' + record['stages'][-1]['status']
        else:
            support = Path(str(explanation) + '.ofn')
            if external:
                generated = json.loads((output / 'external/generation.json').read_text())
                assert generated['status'] == 'generated_requires_independent_verification'
                assert digest(output / 'external/support.ofn') == generated['support_sha256']
                shutil.copyfile(output / 'external/support.ofn', support)
                record['justification_axioms'] = generated['axiom_count']
                record['method'] = generated['method']
                record['external_generator_sha256'] = digest(Path(__file__).with_name('external_justification.py'))
            elif native:
                response = json.loads((output / 'generation.stdout').read_text())
                support.write_text(native_support(response, generator['id']))
                record['native_response_sha256'] = digest(output / 'generation.stdout')
                record['native_adapter_sha256'] = digest(Path(__file__).with_name('native_justification.py'))
                assert digest(module) == module_hash, 'generator changed frozen input'
            else:
                lines = explanation.read_text().splitlines()
                assert lines[-1] == 'Z\tcomplete', 'incomplete generation output'
                assert 'M\tentailed\ttrue' in lines, 'generator did not establish entailment'
                assert digest(output / 'module.ofn') == module_hash, 'generator changed frozen module'
                record['justification_axioms'] = sum(line.startswith('A\t') for line in lines)
            record['justification_sha256'] = digest(support)
            verification = output / 'verification.tsv'
            command = java + ['-cp', str(verifier_classes) + ':' + verifier['path'],
                              'org.kmbenchmark.VerifyJustification', verifier['factory'], str(source),
                              str(support), sub, sup, str(verification)]
            if not run(command, 'verification'):
                record['status'] = 'verification_' + record['stages'][-1]['status']
            else:
                checked = verification.read_text().splitlines()
                assert checked[-1] == 'Z\tcomplete', 'incomplete verification output'
                for field in ['source_subset', 'entailed', 'subset_minimal']:
                    assert 'M\t' + field + '\ttrue' in checked, 'failed verification: ' + field
                record.update(status='independently_verified', verification_sha256=digest(verification))
    except Exception as error:
        record.update(status='adapter_or_validation_error', error=str(error))
    record['files'] = {p.name: {'sha256': digest(p), 'bytes': p.stat().st_size}
                       for p in output.iterdir() if p.is_file() and p.name != 'record.json'}
    publish()
    return record
