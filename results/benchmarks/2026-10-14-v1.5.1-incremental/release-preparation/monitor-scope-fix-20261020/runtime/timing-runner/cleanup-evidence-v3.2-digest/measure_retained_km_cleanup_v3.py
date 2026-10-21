"""Measure KM source updates, preserving the engine's actual reuse receipts."""
import json
import os
from pathlib import Path
import sys
import subprocess
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import tree_watchdog as watchdog
from process_tree_subreaper_v3 import SubreaperScope
from measure_retained_java import digest
from timing_support import exchange_line, km_environment, recorded_environment


def measure(row, revisions, output, timeout=240, memory_mib=20480,
            sample_interval=0.02, km_overrides=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    record = {'schema': 2, 'runner_version': 'cleanup_evidence_v3', 'baseline': 'km', 'mode': 'incremental-source JSONL retained session',
              'artifact_sha256': row['sha256'], 'runner_sha256': digest(__file__),
              'watchdog_sha256': digest(watchdog.__file__),
              'process_tree_cleanup_helper_sha256': digest(Path(__file__).with_name('process_tree_subreaper_v3.py')),
              'process_tree_cleanup_method': 'linux_prctl_subreaper_and_proc_parent_tree',
              'timeout_per_revision_s': timeout,
              'memory_mib': memory_mib, 'cpu_threads': 1,
              'watchdog_sample_interval_s': sample_interval,
              'revisions': [], 'status': 'preparing',
              'host': os.uname().nodename, 'slurm_job_id': os.getenv('SLURM_JOB_ID')}
    def publish():
        temporary = output / 'record.json.part'
        temporary.write_text(json.dumps(record, indent=2) + '\n')
        temporary.replace(output / 'record.json')
    process = None
    observer = None
    process_scope = None
    publish()
    try:
        assert digest(row['path']) == row['sha256'], 'artifact hash mismatch'
        for revision in revisions:
            assert digest(revision['path']) == revision['sha256'], 'source hash mismatch'
        cpu = min(os.sched_getaffinity(0))
        env = km_environment(overrides=km_overrides)
        record['effective_environment'] = recorded_environment(env)
        command = [row['path'], 'incremental-source']
        record.update(command=command, cpu_affinity=[cpu], status='running')
        def child():
            watchdog.child_preexec()
            os.sched_setaffinity(0, {cpu})
        watchdog.protect_supervisor()
        # Exclude subreaper preflight / full /proc scan from comparable work.
        process_scope = SubreaperScope().begin()
        started = time.monotonic()
        with (output / 'stderr').open('wb') as stderr:
            spawn_started = started
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=stderr, env=env, preexec_fn=child)
            record['actual_pid'] = process.pid
            registration_started = time.monotonic()
            process_scope.register_root(process.pid)
            registration_finished = time.monotonic()
            from timing_support import start_exit_observer, stop_exit_observer
            observer = start_exit_observer(process)
            spawn_finished = time.monotonic()
            record['cleanup_root_registration_wall_s'] = registration_finished - registration_started
            for index, revision in enumerate(revisions):
                stage = dict(revision, revision=index, status='running', semantic_validation='pending')
                record['revisions'].append(stage)
                publish()
                # Start after durable harness publication. Source read and JSON
                # serialization remain part of the measured request/response.
                phase_start = time.monotonic()
                operation = revision.get('operation', 'init' if index == 0 else 'replace')
                message = {'op': operation}
                if operation in ('init', 'replace'):
                    message['functional_syntax'] = Path(revision['path']).read_text()
                request = (json.dumps(message,
                                     ensure_ascii=False) + '\n').encode()
                completed = threading.Event()
                received = {}
                def exchange():
                    received.update(exchange_line(process, request))
                    completed.set()
                transfer = threading.Thread(target=exchange, daemon=True)
                transfer.start()
                def checkpoint(status, peak):
                    stage.update(status=status, sampled_peak_bytes=peak)
                    record['status'] = status
                    publish()
                result = watchdog.monitor(process, timeout=max(0, timeout - (time.monotonic() - phase_start)),
                                          memcap_bytes=memory_mib * 1024**2,
                                          until=completed.is_set, on_trip=checkpoint,
                                          sample_interval=sample_interval, wake_event=completed)
                monitor_return_monotonic = time.monotonic()
                transfer.join(timeout=5)
                if transfer.is_alive():
                    raise RuntimeError('I/O thread did not stop after worker termination')
                line_observed = received.get('line_observed_monotonic')
                complete_line = received.get('complete_line', False)
                if line_observed is not None:
                    response_wall = line_observed - phase_start
                    stage.update(response_line_wall_s=response_wall,
                                 response_line_complete=complete_line,
                                 response_line_observed_monotonic=line_observed)
                else:
                    response_wall = None
                if response_wall is not None:
                    measured_wall = response_wall
                    wall_basis = ('exchange_thread_complete_response_line' if complete_line
                                  else 'exchange_thread_incomplete_line_or_eof')
                else:
                    measured_wall = max(0.0, monitor_return_monotonic - phase_start)
                    wall_basis = 'watchdog_terminal_or_worker_exit_observation'
                stage.update(status=result.status, wall_s=measured_wall,
                             wall_s_basis=wall_basis,
                             watchdog_wall_s=result.wall_s,
                             watchdog_monitor_return_monotonic=monitor_return_monotonic,
                             sampled_peak_bytes=result.peak_bytes, request_bytes=len(request))
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
                expected_status = revision.get('expected_response_status', 'ok')
                if response.get('status') != expected_status:
                    stage['status'] = 'unexpected_response_status'
                    stage['expected_response_status'] = expected_status
                    stage['actual_response_status'] = response.get('status')
                    record['status'] = stage['status']
                    publish()
                    break
                if expected_status != 'ok':
                    stage['status'] = 'expected_refusal_unvalidated'
                    stage['response_error'] = response.get('error')
                    stage['actual_response_status'] = expected_status
                    publish()
                    continue
                if 'result' not in response:
                    stage['status'] = 'engine_refusal_or_error'
                    record['status'] = stage['status']
                    break
                stage['status'] = 'executed_unvalidated'
                publish()
            process.stdin.close()
            shutdown_started = time.monotonic()
            if process.poll() is None:
                shutdown = watchdog.monitor(process, timeout=10, memcap_bytes=memory_mib * 1024**2,
                                            sample_interval=sample_interval, wake_event=observer[3])
                record['shutdown'] = {'status': shutdown.status, 'exit_code': process.returncode,
                                      'watchdog_wall_s': shutdown.wall_s}
            shutdown_finished = time.monotonic()
            stop_exit_observer(observer, process)
            observed_exit = observer[2].get('monotonic')
            child_exit_wall = (observed_exit - started) if observed_exit is not None else None
            call_sum = sum(r.get('wall_s', 0.0) for r in record['revisions']
                           if isinstance(r.get('wall_s'), (int, float)))
            spawn_wall = spawn_finished - spawn_started
            shutdown_wall = ((observed_exit - shutdown_started) if observed_exit is not None
                             else shutdown_finished - shutdown_started)
            comparable = spawn_wall + call_sum + max(0.0, shutdown_wall)
            record.update(
                process_spawn_wall_s=spawn_wall,
                process_shutdown_wall_s=max(0.0, shutdown_wall),
                comparable_call_sum_wall_s=call_sum,
                comparable_whole_session_wall_s=comparable,
                child_lifecycle_observed_wall_s=child_exit_wall,
                harness_gaps_wall_s=(max(0.0, child_exit_wall - comparable)
                                     if child_exit_wall is not None else None),
                observer_method=observer[2].get('method'),
                observer_fallback_poll_interval_s=observer[2].get('fallback_poll_interval_s'),
                watchdog_adapter_return_wall_s=time.monotonic() - started,
                exit_code=process.returncode)
            record['total_wall_s'] = record['child_lifecycle_observed_wall_s']
            allowed_terminal_steps = {'executed_unvalidated', 'expected_refusal_unvalidated'}
            if len(record['revisions']) == len(revisions) and all(r['status'] in allowed_terminal_steps for r in record['revisions']):
                record['status'] = 'executed_unvalidated' if process.returncode == 0 else 'shutdown_error'
    except Exception as error:
        record.update(status='adapter_error', error=str(error))
        if record['revisions'] and record['revisions'][-1]['status'] in ['running', 'ready']:
            record['revisions'][-1].update(status='adapter_error', error=str(error))
    finally:
        try:
            if process is not None:
                if process.poll() is None:
                    try:
                        _, members = watchdog.tree_and_group_rss(
                            process.pid, process.pid, watchdog.snapshot_all())
                        watchdog.kill_tree(members)
                    except Exception as error:
                        record['watchdog_tree_cleanup_error'] = repr(error)
                    if process.poll() is None:
                        try:
                            process.kill()
                        except ProcessLookupError:
                            pass
                    try:
                        process.wait(timeout=5)
                    except Exception as error:
                        record['root_process_wait_error'] = repr(error)
                if observer is not None:
                    try:
                        stop_exit_observer(observer, process)
                    except RuntimeError:
                        pass
                for pipe in [process.stdin, process.stdout]:
                    if pipe and not pipe.closed:
                        try:
                            pipe.close()
                        except Exception as error:
                            record.setdefault('pipe_close_errors', []).append(repr(error))
        finally:
            if process_scope is not None:
                try:
                    cleanup = process_scope.finish()
                except Exception as error:
                    cleanup = {'status': 'unknown', 'remaining_processes': None,
                               'subreaper_restored': False,
                               'method': 'linux_prctl_subreaper_and_proc_parent_tree',
                               'error': repr(error)}
                record['child_tree_cleanup'] = cleanup
                record['cleanup_root_pid'] = process_scope.root_pid
                record['cleanup_root_starttime'] = process_scope.root_starttime
                record['remaining_processes'] = cleanup.get('remaining_processes')
                record['subreaper_restored'] = cleanup.get('subreaper_restored', False)
    for index in range(len(record['revisions']), len(revisions)):
        record['revisions'].append(dict(revisions[index], revision=index, status='not_run_after_session_failure'))
    publish()
    return record
