"""Measure source revisions in one OWLAPI session with per-revision limits."""
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
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()


def measure(row, revisions, classes, output, java='java', timeout=240, memory_mib=20480):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    classes = Path(classes).resolve()
    record = {'baseline': row['id'], 'mode': 'retained OWLAPI object with flush',
              'internal_reuse': 'not inferred from interface', 'artifact_sha256': row['sha256'],
              'runner_sha256': digest(__file__), 'watchdog_sha256': digest(watchdog.__file__),
              'timeout_per_revision_s': timeout, 'memory_mib': memory_mib, 'cpu_threads': 1,
              'peak_method': 'sampled full process-tree RSS per revision', 'revisions': [],
              'status': 'preparing', 'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID')}
    def publish():
        temporary = output / 'record.json.part'
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        temporary.replace(output / 'record.json')
    publish()
    process = None
    try:
        assert digest(row['path']) == row['sha256'], 'runtime hash mismatch'
        for revision in revisions:
            assert digest(revision['path']) == revision['sha256'], 'revision hash mismatch'
            assert '\n' not in str(revision['path']), 'newline in revision path'
        record['classes'] = {str(p.relative_to(classes)): digest(p) for p in classes.rglob('*.class')}
        assert 'org/kmbenchmark/IncrementalClassifier.class' in record['classes'], 'missing worker'
        cpu = min(os.sched_getaffinity(0))
        command = [java, '-Xms256m', '-Xmx16g', '-XX:ActiveProcessorCount=1', '-cp',
                   str(classes) + ':' + row['path'], 'org.kmbenchmark.IncrementalClassifier',
                   row['factory'], str(output / 'session'), '--stdin']
        record.update(command=command, cpu_affinity=[cpu], status='running')
        publish()
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        watchdog.protect_supervisor()
        started = time.monotonic()
        with (output / 'stdout').open('wb') as stdout, (output / 'stderr').open('wb') as stderr:
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=stdout, stderr=stderr,
                                       preexec_fn=child)
            for index, revision in enumerate(revisions):
                stage = dict(revision, revision=index, status='running', semantic_validation='pending')
                record['revisions'].append(stage)
                publish()
                marker = output / 'session' / f'{index:03}.timing.tsv'
                process.stdin.write((str(Path(revision['path']).resolve()) + '\n').encode())
                process.stdin.flush()
                def checkpoint(status, peak):
                    stage.update(status=status, sampled_peak_bytes=peak)
                    record['status'] = status
                    publish()
                result = watchdog.monitor(process, timeout=timeout, memcap_bytes=memory_mib * 1024**2,
                                          until=marker.exists, on_trip=checkpoint)
                stage.update(status=result.status, wall_s=result.wall_s, sampled_peak_bytes=result.peak_bytes)
                if result.status != 'ready':
                    if result.status == 'ok':
                        stage['status'] = 'worker_exited_before_revision_completed'
                    record['status'] = stage['status']
                    publish()
                    break
                taxonomy = output / 'session' / f'{index:03}.taxonomy.tsv'
                with taxonomy.open('rb') as stream:
                    stream.seek(max(0, taxonomy.stat().st_size - 32))
                    assert stream.read().endswith(b'Z\tcomplete\n'), 'incomplete taxonomy'
                stage.update(status='executed_unvalidated', taxonomy_sha256=digest(taxonomy),
                             timing_sha256=digest(marker))
                publish()
            process.stdin.close()
            if process.poll() is None:
                shutdown = watchdog.monitor(process, timeout=10, memcap_bytes=memory_mib * 1024**2)
                record['shutdown'] = {'status': shutdown.status, 'exit_code': process.returncode}
            if len(record['revisions']) == len(revisions) and all(r['status'] == 'executed_unvalidated' for r in record['revisions']):
                record['status'] = ('executed_unvalidated' if process.returncode == 0 and
                                    (output / 'session/COMPLETE').is_file() else 'shutdown_error')
            record.update(total_wall_s=time.monotonic() - started, exit_code=process.returncode)
    except Exception as error:
        record.update(status='adapter_error', error=str(error))
        if record['revisions'] and record['revisions'][-1]['status'] in ['running', 'ready']:
            record['revisions'][-1].update(status='adapter_error', error=str(error))
    finally:
        if process is not None:
            if process.poll() is None:
                _, members = watchdog.tree_and_group_rss(process.pid, process.pid, watchdog.snapshot_all())
                watchdog.kill_tree(members)
                process.wait()
            if process.stdin and not process.stdin.closed:
                process.stdin.close()
    for index in range(len(record['revisions']), len(revisions)):
        record['revisions'].append(dict(revisions[index], revision=index, status='not_run_after_session_failure'))
    publish()
    return record
