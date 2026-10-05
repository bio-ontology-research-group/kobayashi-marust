"""Measure KM source updates, preserving the engine's actual reuse receipts."""
import json
import os
from pathlib import Path
import subprocess
import threading
import time

import tree_watchdog as watchdog
from measure_retained_java import digest


def measure(row, revisions, output, timeout=240, memory_mib=20480):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    record = {'baseline': 'km', 'mode': 'incremental-source JSONL retained session',
              'artifact_sha256': row['sha256'], 'runner_sha256': digest(__file__),
              'watchdog_sha256': digest(watchdog.__file__), 'timeout_per_revision_s': timeout,
              'memory_mib': memory_mib, 'cpu_threads': 1, 'revisions': [], 'status': 'preparing',
              'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID')}
    def publish():
        temporary = output / 'record.json.part'
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        temporary.replace(output / 'record.json')
    process = None
    publish()
    try:
        assert digest(row['path']) == row['sha256'], 'artifact hash mismatch'
        for revision in revisions:
            assert digest(revision['path']) == revision['sha256'], 'source hash mismatch'
        cpu = min(os.sched_getaffinity(0))
        env = dict(os.environ, KM_THREADS='1', RAYON_NUM_THREADS='1', OMP_NUM_THREADS='1')
        command = [row['path'], 'incremental-source']
        record.update(command=command, cpu_affinity=[cpu], status='running')
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        watchdog.protect_supervisor()
        started = time.monotonic()
        with (output / 'stderr').open('wb') as stderr:
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=stderr, env=env, preexec_fn=child)
            for index, revision in enumerate(revisions):
                phase_start = time.monotonic()
                stage = dict(revision, revision=index, status='running', semantic_validation='pending')
                record['revisions'].append(stage)
                publish()
                request = (json.dumps({'op': 'init' if index == 0 else 'replace',
                                      'functional_syntax': Path(revision['path']).read_text()},
                                     ensure_ascii=False) + '\n').encode()
                completed = threading.Event()
                received = {}
                def exchange():
                    try:
                        process.stdin.write(request)
                        process.stdin.flush()
                        received['raw'] = process.stdout.readline()
                    except Exception as error:
                        received['error'] = str(error)
                    finally:
                        completed.set()
                transfer = threading.Thread(target=exchange, daemon=True)
                transfer.start()
                def checkpoint(status, peak):
                    stage.update(status=status, sampled_peak_bytes=peak)
                    record['status'] = status
                    publish()
                result = watchdog.monitor(process, timeout=max(0, timeout - (time.monotonic() - phase_start)),
                                          memcap_bytes=memory_mib * 1024**2, until=completed.is_set, on_trip=checkpoint)
                stage.update(status=result.status, wall_s=time.monotonic() - phase_start,
                             sampled_peak_bytes=result.peak_bytes, request_bytes=len(request))
                transfer.join(timeout=5)
                if transfer.is_alive():
                    raise RuntimeError('I/O thread did not stop after worker termination')
                del request
                if result.status != 'ready':
                    if result.status == 'ok':
                        stage['status'] = 'worker_exited_before_response'
                    record['status'] = stage['status']
                    break
                if 'error' in received:
                    raise RuntimeError('JSONL transfer failed: ' + received['error'])
                raw = received.get('raw', b'')
                if not raw.endswith(b'\n'):
                    raise RuntimeError('worker closed stdout without a complete response')
                response_path = output / f'{index:03}.response.json'
                response_path.write_bytes(raw)
                response = json.loads(raw)
                stage.update(response_sha256=digest(response_path), engine_status=response.get('status'),
                             route=response.get('route'), retained_backend=response.get('retained_backend'),
                             reuse_receipt=response.get('receipt'))
                if response.get('status') != 'ok' or 'result' not in response:
                    stage['status'] = 'engine_refusal_or_error'
                    record['status'] = stage['status']
                    break
                stage['status'] = 'executed_unvalidated'
                publish()
            process.stdin.close()
            if process.poll() is None:
                shutdown = watchdog.monitor(process, timeout=10, memcap_bytes=memory_mib * 1024**2)
                record['shutdown'] = {'status': shutdown.status, 'exit_code': process.returncode}
            record.update(total_wall_s=time.monotonic() - started, exit_code=process.returncode)
            if len(record['revisions']) == len(revisions) and all(r['status'] == 'executed_unvalidated' for r in record['revisions']):
                record['status'] = 'executed_unvalidated' if process.returncode == 0 else 'shutdown_error'
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
            for pipe in [process.stdin, process.stdout]:
                if pipe and not pipe.closed:
                    pipe.close()
    for index in range(len(record['revisions']), len(revisions)):
        record['revisions'].append(dict(revisions[index], revision=index, status='not_run_after_session_failure'))
    publish()
    return record
