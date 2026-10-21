"""Measure one public OWLAPI sequence; no semantic acceptance is inferred here."""
import json
import os
from pathlib import Path
import queue
import signal
import subprocess
import sys
import threading
import time

_INCREMENTAL_RESULTS = Path(__file__).resolve().parents[2]
_TIMING_RUNNER = _INCREMENTAL_RESULTS / 'timing-runner'
sys.path.insert(0, str(_TIMING_RUNNER))
sys.path.insert(0, str(_TIMING_RUNNER / 'cleanup-evidence-v3.2-digest'))
import tree_watchdog as watchdog
from scoped_snapshot import ScopedSnapshot
from process_tree_subreaper_v3 import SubreaperScope
from timing_support import km_environment, recorded_environment, start_exit_observer, stop_exit_observer
from run_panel import sha256, write_json


def measure(binding, revisions, mode, output, cpu, timeout=240, memory_mib=20480, heap='16g'):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    record = {'schema': 2, 'runner_version': 'owlapi_cleanup_v3_scoped_snapshot_v1',
              'status': 'preparing', 'mode': mode, 'binding': binding,
              'process_tree_cleanup_method': 'linux_prctl_subreaper_and_proc_parent_tree',
              'timeout_per_revision_s': timeout, 'memory_mib': memory_mib,
              'cpu': cpu, 'heap': heap, 'revisions': [], 'performance_claim': False,
              'timing_basis': 'complete stdout event arrival, not watchdog polling',
              'native_counters': 'only actual reflected fields; absent means unavailable'}
    publish = lambda: write_json(output / 'record.json', record)
    publish()
    env = km_environment()
    for name in ('JAVA_TOOL_OPTIONS', 'JDK_JAVA_OPTIONS', '_JAVA_OPTIONS'):
        env.pop(name, None)
    record['environment'] = recorded_environment(env)
    command = [binding['java'], '-Xms256m', '-Xmx' + heap, '-XX:ActiveProcessorCount=1',
               '-Djava.awt.headless=true', '-Dkm.timeout.seconds=' + str(timeout),
               '-Dkm.bin=' + binding['binary'], '-cp', binding['classpath'],
               'org.kmbenchmark.IncrementalClassifier',
               'org.bioontology.kobayashimarust.protege.KMReasonerFactory',
               str(output / 'session'), mode, '--stdin']
    record['command'] = command
    process = None
    observer = None
    scoped_snapshot = None
    process_scope = None
    tracked = {}
    events = queue.Queue()
    available = threading.Event()
    reader = None
    started = time.monotonic()

    def sample(members=None):
        if members is None:
            snap = watchdog.snapshot_all()
            _, members = watchdog.tree_and_group_rss(process.pid, process.pid, snap)
        for pid in members:
            try:
                fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
                tracked[pid] = (int(fields[19]), int(fields[2]))
            except (OSError, IndexError, ValueError):
                pass

    def child():
        watchdog.child_preexec()
        os.sched_setaffinity(0, {cpu})

    def wait_event():
        def checkpoint(status, peak):
            record.update(status=status, terminal_peak_bytes=peak, resource_trip=status)
            publish()
        def ready():
            return not events.empty()
        result = watchdog.monitor(process, timeout=timeout, memcap_bytes=memory_mib * 1024**2,
                                  until=ready, wake_event=available, on_trip=checkpoint,
                                  snapshotter=scoped_snapshot, on_sample=sample)
        if events.empty():
            raise RuntimeError('event wait ended without event: ' + result.status)
        item = events.get_nowait()
        available.clear()
        if not events.empty():
            available.set()
        if item[0] is None:
            raise RuntimeError('worker stdout EOF before expected event')
        if result.status not in ('ready', 'ok'):
            raise RuntimeError('event resource failure: ' + result.status)
        return item, result

    try:
        watchdog.protect_supervisor()
        # Keep preflight outside the existing spawn/READY and request timers.
        cleanup_preflight_started = time.monotonic()
        process_scope = SubreaperScope().begin()
        with (output / 'stdout').open('wb') as stdout, (output / 'stderr').open('wb') as stderr:
            spawn = time.monotonic()
            record['cleanup_preflight_wall_s'] = spawn - cleanup_preflight_started
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                       stderr=stderr, env=env, preexec_fn=child)
            record['actual_pid'] = process.pid
            scoped_snapshot = ScopedSnapshot(process.pid)
            registration_started = time.monotonic()
            process_scope.register_root(process.pid)
            record['cleanup_root_registration_wall_s'] = time.monotonic() - registration_started
            record['cleanup_root_starttime'] = process_scope.root_starttime
            observer = start_exit_observer(process)

            def read_events():
                while True:
                    line = process.stdout.readline()
                    observed = time.monotonic()
                    if line:
                        stdout.write(line)
                        stdout.flush()
                    events.put((line if line else None, observed))
                    available.set()
                    if not line:
                        return

            reader = threading.Thread(target=read_events, daemon=True)
            reader.start()
            (raw, ready_time), result = wait_event()
            if raw != b'READY\n':
                raise ValueError('unexpected READY event: ' + repr(raw))
            record.update(status='running', launch_to_ready_wall_s=ready_time - spawn,
                          initialization_peak_bytes=result.peak_bytes)
            publish()
            for index, revision in enumerate(revisions):
                stage = dict(revision, revision=index, status='running')
                record['revisions'].append(stage)
                publish()
                call = time.monotonic()
                process.stdin.write((revision['path'] + '\n').encode())
                process.stdin.flush()
                (raw, observed), result = wait_event()
                stage.update(wall_s=observed - call, sampled_peak_bytes=result.peak_bytes,
                             raw_event=raw.decode('utf-8', 'replace'), status='terminal_before_audit')
                publish()
                fields = raw.decode().rstrip('\n').split('\t')
                if len(fields) != 3 or fields[:2] != ['DONE', str(index)]:
                    raise ValueError('unexpected DONE event: ' + repr(raw))
                timing = output / 'session' / f'{index:03}.timing.json'
                stage.update(worker_timing_sha256=sha256(timing), worker=json.loads(timing.read_text()),
                             status=fields[2])
                publish()
            shutdown = time.monotonic()
            process.stdin.close()
            (raw, _), result = wait_event()
            if raw != b'COMPLETE\n':
                raise ValueError('unexpected COMPLETE event: ' + repr(raw))
            terminal = watchdog.monitor(process, timeout=10, memcap_bytes=memory_mib * 1024**2,
                                        wake_event=observer[3], snapshotter=scoped_snapshot, on_sample=sample)
            stop_exit_observer(observer, process)
            exit_time = observer[2].get('monotonic', time.monotonic())
            record.update(actual_exit_code=process.returncode, shutdown_wall_s=max(0, exit_time - shutdown),
                          observer_method=observer[2].get('method'), shutdown_status=terminal.status,
                          child_lifecycle_wall_s=exit_time - spawn)
            call_sum = sum(row['wall_s'] for row in record['revisions'])
            record.update(call_sum_wall_s=call_sum,
                          comparable_whole_sequence_wall_s=record['launch_to_ready_wall_s'] + call_sum + record['shutdown_wall_s'])
            record['status'] = 'executed_unvalidated' if process.returncode == 0 else 'process_error'
    except Exception as error:
        record.update(status='adapter_or_resource_error', error=repr(error))
    finally:
        cleanup_errors = []
        if process is not None:
            try:
                sample()
            except Exception as error:
                cleanup_errors.append('final process sample: ' + repr(error))
            # Keep the existing group/PID cleanup as a first pass. The
            # subreaper proof below is authoritative for escaped descendants.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            except OSError as error:
                cleanup_errors.append('kill launched process group: ' + repr(error))
            for pid, identity in tracked.items():
                try:
                    fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
                    if (int(fields[19]), int(fields[2])) == identity:
                        os.kill(pid, signal.SIGKILL)
                except (ProcessLookupError, FileNotFoundError):
                    pass
                except (OSError, IndexError, ValueError) as error:
                    cleanup_errors.append(f'kill sampled PID {pid}: ' + repr(error))
            if process.stdin and not process.stdin.closed:
                try:
                    process.stdin.close()
                except OSError as error:
                    cleanup_errors.append('close worker stdin: ' + repr(error))
            try:
                process.wait()
            except Exception as error:
                cleanup_errors.append('wait for launched root: ' + repr(error))
            if observer:
                try:
                    stop_exit_observer(observer, process)
                except Exception as error:
                    cleanup_errors.append('stop exit observer: ' + repr(error))
            record['actual_exit_code'] = process.returncode
        if process_scope is not None:
            try:
                cleanup = process_scope.finish()
                record['child_tree_cleanup'] = cleanup
                record['cleanup_root_pid'] = process_scope.root_pid
                record['cleanup_root_starttime'] = process_scope.root_starttime
                record['remaining_processes'] = cleanup.get('remaining_processes')
            except Exception as cleanup_error:
                record['child_tree_cleanup'] = {
                    'method': 'linux_prctl_subreaper_and_proc_parent_tree',
                    'status': 'unknown', 'remaining_processes': None,
                    'subreaper_restored': False, 'error': repr(cleanup_error)}
                record['remaining_processes'] = None
        else:
            record['child_tree_cleanup'] = {
                'method': 'linux_prctl_subreaper_and_proc_parent_tree',
                'status': 'unknown', 'remaining_processes': None,
                'subreaper_restored': False, 'error': 'subreaper scope was not started'}
            record['remaining_processes'] = None
        # The subreaper cleanup must precede joining the pipe reader: an
        # escaped descendant may inherit stdout and keep readline blocked.
        if reader:
            reader.join(timeout=5)
            if reader.is_alive():
                cleanup_errors.append('stdout reader remained blocked after child-tree cleanup')
        if process is not None and process.stdout and not process.stdout.closed and (not reader or not reader.is_alive()):
            process.stdout.close()
        if process is not None:
            try:
                snap = watchdog.snapshot_all()
                _, remaining = watchdog.tree_and_group_rss(process.pid, process.pid, snap)
                record['remaining_process_tree_or_group'] = sorted(remaining)
            except Exception as error:
                cleanup_errors.append('final process-group observation: ' + repr(error))
                record['remaining_process_tree_or_group'] = None
        else:
            record['remaining_process_tree_or_group'] = None
        record['cleanup_errors'] = cleanup_errors
        record.update(adapter_lifecycle_wall_s=time.monotonic() - started,
                      tracked_process_start_and_group={str(k): list(v) for k, v in tracked.items()},
                      stdout_sha256=sha256(output / 'stdout') if (output / 'stdout').exists() else None,
                      stderr_sha256=sha256(output / 'stderr') if (output / 'stderr').exists() else None)
        if scoped_snapshot is not None:
            record['process_sampling'] = scoped_snapshot.summary()
        # Exit/resource evidence is durable before the panel's semantic parser.
        publish()
    return record
