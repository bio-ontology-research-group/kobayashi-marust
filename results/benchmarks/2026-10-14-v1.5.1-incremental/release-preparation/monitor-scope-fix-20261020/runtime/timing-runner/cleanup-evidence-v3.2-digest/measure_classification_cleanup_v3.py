"""Run one frozen baseline under the common classification resource protocol.

This records execution and raw output. A completed process is deliberately not
labelled a correct classification: independent semantic validation is separate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import subprocess
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import tree_watchdog as watchdog
from process_tree_subreaper_v3 import SubreaperScope
from timing_support import km_environment, recorded_environment, start_exit_observer, stop_exit_observer


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def measure(inventory, baseline, source, source_sha256, output, runtime_source=None,
            runtime_sha256=None, timeout=240, memory_mib=20480, conversion_receipt=None,
            sample_interval=0.02, observer_poll_interval_s=0.001,
            time_binary='/usr/bin/time', km_overrides=None):
    source, output = Path(source).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    runtime_source = Path(runtime_source).resolve() if runtime_source else source
    row = next(r for r in inventory['artifacts'] if r['id'] == baseline)
    record = {'schema': 2, 'runner_version': 'cleanup_evidence_v3', 'baseline': baseline, 'source': str(source), 'source_sha256': source_sha256,
              'runtime_source': str(runtime_source), 'artifact': row['path'], 'artifact_sha256': row['sha256'],
              'runner_sha256': digest(__file__), 'watchdog_sha256': digest(watchdog.__file__),
              'process_tree_cleanup_helper_sha256': digest(Path(__file__).with_name('process_tree_subreaper_v3.py')),
              'process_tree_cleanup_method': 'linux_prctl_subreaper_and_proc_parent_tree',
              'timeout_s': timeout, 'memory_mib': memory_mib, 'cpu_threads': 1,
              'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID'),
              'status': 'preparing', 'semantic_validation': 'pending'}

    def publish():
        tmp = output / 'record.json.part'
        tmp.write_text(json.dumps(record, indent=2) + '\n')
        tmp.replace(output / 'record.json')

    publish()
    process_scope = None
    proc = None
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
        if baseline == 'km':
            env = km_environment(overrides=km_overrides)
            explicit = recorded_environment(env)
        else:
            env = dict(os.environ)
            java_opts = '-Xms256m -Xmx16g -XX:ActiveProcessorCount=1'
            explicit = {'OMP_NUM_THREADS': '1', 'RAYON_NUM_THREADS': '1', 'KM_THREADS': '1',
                        'KM_ROUTE': 'auto', 'JAVA_OPTS': java_opts}
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
                      external_time_wrapper=time_binary,
                      cpu_affinity=[cpu], status='running')
        publish()
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        # Exclude subreaper preflight / full /proc scan from classification time.
        process_scope = SubreaperScope().begin()
        started = time.monotonic()
        def checkpoint(status, peak):
            record.update(status=status, peak_bytes=peak, wall_s=time.monotonic() - started)
            publish()
        watchdog.protect_supervisor()
        measured_command = command if time_binary is None else [
            time_binary, '-f', '%M', '-o', str(output / 'max-rss-kib.txt')
        ] + command
        with (taxonomy if stdout_is_taxonomy else output / 'stdout').open('wb') as stdout, (output / 'stderr').open('wb') as stderr:
            proc = subprocess.Popen(measured_command, stdout=stdout, stderr=stderr, stdin=subprocess.DEVNULL,
                                    env=env, preexec_fn=child)
            record['actual_pid'] = proc.pid
            registration_started = time.monotonic()
            process_scope.register_root(proc.pid)
            registration_finished = time.monotonic()
            observer = start_exit_observer(proc, poll_interval_s=observer_poll_interval_s)
            record['cleanup_root_registration_wall_s'] = registration_finished - registration_started
            result = watchdog.monitor(proc, timeout=timeout, memcap_bytes=memory_mib * 1024**2,
                                      sample_interval=sample_interval, on_trip=checkpoint)
            stop_exit_observer(observer, proc)
        observed_exit = observer[2]
        watchdog_wall = result.wall_s
        if result.status not in ('timeout', 'memout') and 'monotonic' in observed_exit:
            wall = observed_exit['monotonic'] - started
            wall_basis = 'kernel_pidfd_exit_readiness' if observed_exit.get('method') == 'pidfd_select' else 'process_exit_observer_poll_fallback'
        else:
            wall = watchdog_wall
            wall_basis = 'watchdog_terminal'
        peak = result.peak_bytes
        max_rss_path = output / 'max-rss-kib.txt'
        for line in max_rss_path.read_text().splitlines() if max_rss_path.is_file() else ():
            if line.isdigit():
                peak = max(peak, int(line) * 1024)
        record.update(status=result.status, exit_code=proc.returncode, wall_s=wall,
                      wall_s_basis=wall_basis, watchdog_wall_s=watchdog_wall,
                      watchdog_sample_interval_s=sample_interval,
                      process_exit_observer_poll_interval_s=observer_poll_interval_s,
                      process_exit_observed_monotonic=observed_exit.get('monotonic'),
                      process_exit_observer_method=observed_exit.get('method'),
                      process_exit_observer_fallback_poll_interval_s=observed_exit.get('fallback_poll_interval_s'),
                      process_exit_observer_returncode=observed_exit.get('returncode'),
                      observer_returncode_matches_reaped_process=(
                          observed_exit.get('returncode') == proc.returncode
                          if 'returncode' in observed_exit else None),
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
    finally:
        if proc is not None and proc.poll() is None:
            try:
                proc.kill()
                proc.wait()
            except Exception as error:
                record['root_process_cleanup_error'] = repr(error)
        if process_scope is not None:
            cleanup = process_scope.finish()
            record['child_tree_cleanup'] = cleanup
            record['cleanup_root_pid'] = process_scope.root_pid
            record['cleanup_root_starttime'] = process_scope.root_starttime
            record['remaining_processes'] = cleanup.get('remaining_processes')
            record['subreaper_restored'] = cleanup.get('subreaper_restored', False)
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
