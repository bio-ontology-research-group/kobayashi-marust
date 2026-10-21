"""Shared timing helpers for matched fresh and retained KM measurements."""
import os
import select
import threading
import time


KM_CONFIG = {
    "KM_ROUTE": "auto",
    "KM_THREADS": "1",
}
THREAD_CONFIG = {
    "OMP_NUM_THREADS": "1",
    "RAYON_NUM_THREADS": "1",
}


def km_environment(parent=None, overrides=None):
    """Drop inherited KM switches, then apply the same explicit config to both arms."""
    env = dict(os.environ if parent is None else parent)
    for key in tuple(env):
        if key.startswith("KM_"):
            del env[key]
    for key in THREAD_CONFIG:
        env.pop(key, None)
    env.pop("JAVA_OPTS", None)
    env.update(KM_CONFIG)
    env.update(THREAD_CONFIG)
    for key, value in (overrides or {}).items():
        if not (key.startswith('KM_') or key in THREAD_CONFIG):
            raise ValueError(f'unsupported KM runtime override: {key}')
        env[key] = str(value)
    return env


def recorded_environment(env):
    return {
        "km": {key: env[key] for key in sorted(env) if key.startswith("KM_")},
        "threading": {key: env[key] for key in sorted(THREAD_CONFIG)},
        "java_opts": env.get("JAVA_OPTS"),
        "inherited_km_variables": "stripped before applying explicit KM_CONFIG",
    }


def exchange_line(process, request):
    """Write one request and timestamp exactly when its complete stdout line arrives."""
    received = {}
    try:
        process.stdin.write(request)
        process.stdin.flush()
        raw = process.stdout.readline()
        observed = time.monotonic()
        received["raw"] = raw
        received["line_observed_monotonic"] = observed
        received["complete_line"] = raw.endswith(b"\n")
    except Exception as error:  # noqa: BLE001 - caller records adapter failures
        received["error"] = str(error)
        received["line_observed_monotonic"] = time.monotonic()
        received["complete_line"] = False
    finally:
        received["exchange_finished_monotonic"] = time.monotonic()
    return received


def start_exit_observer(process, poll_interval_s=0.001):
    """Observe exit via pidfd readiness, with a documented polling fallback.

    The observer uses Popen.poll only after kernel readiness, to reap/cache the
    status through Popen's own synchronization. On kernels without pidfd_open,
    it falls back to bounded Popen.poll sampling and records that resolution.
    """
    stop = threading.Event()
    exited = threading.Event()
    observed = {}
    pidfd = None
    try:
        pidfd = os.pidfd_open(process.pid, 0)
        observed["method"] = "pidfd_select"
    except (AttributeError, OSError):
        observed["method"] = "popen_poll_fallback"
        observed["fallback_poll_interval_s"] = poll_interval_s

    def observe():
        try:
            if pidfd is not None:
                poller = select.poll()
                poller.register(pidfd, select.POLLIN | select.POLLHUP | select.POLLERR)
                while not stop.is_set():
                    if poller.poll(100):
                        # pidfd readiness is terminal. wait() shares Popen's
                        # lock with watchdog waiters, so this cannot steal a
                        # status; it waits out a concurrent reap and returns
                        # Popen's cached code once that waiter releases it.
                        returncode = process.wait()
                        observed["returncode"] = returncode
                        observed["monotonic"] = time.monotonic()
                        exited.set()
                        return
            else:
                while not stop.is_set():
                    returncode = process.poll()
                    if returncode is not None:
                        observed["returncode"] = returncode
                        observed["monotonic"] = time.monotonic()
                        exited.set()
                        return
                    stop.wait(poll_interval_s)
        finally:
            if pidfd is not None:
                os.close(pidfd)

    thread = threading.Thread(target=observe, name="km-exit-observer", daemon=True)
    thread.start()
    return stop, thread, observed, exited


def stop_exit_observer(observer, process=None):
    stop, thread, observed, exited = observer
    # Callers stop only after watchdog termination or process completion. If
    # the thread lost the race to a fast reap, recover the cached terminal
    # status synchronously before asking it to exit.
    if not exited.is_set() and process is not None:
        returncode = process.poll()
        if returncode is not None:
            observed["returncode"] = returncode
            observed["monotonic"] = time.monotonic()
            exited.set()
    stop.set()
    thread.join(timeout=1)
    if thread.is_alive():
        raise RuntimeError("process-exit observer failed to stop")
    if process is not None and process.poll() is not None and not exited.is_set():
        observed["returncode"] = process.returncode
        observed["monotonic"] = time.monotonic()
        exited.set()
