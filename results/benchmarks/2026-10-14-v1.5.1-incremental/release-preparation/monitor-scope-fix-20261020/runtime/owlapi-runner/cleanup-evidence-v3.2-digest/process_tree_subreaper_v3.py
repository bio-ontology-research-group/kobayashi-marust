"""Fail-closed owned-process-tree cleanup evidence using Linux subreaper adoption.

Scope is deliberately limited to one sequential measurement supervisor. It
refuses to start if that supervisor already owns descendants, enables
PR_SET_CHILD_SUBREAPER before launch, and restores the old setting only after
all launched descendants have been killed/reaped and repeated /proc scans agree.
"""
import ctypes
import errno
import os
import signal
import time

PR_SET_CHILD_SUBREAPER = 36
PR_GET_CHILD_SUBREAPER = 37


class TreeObservationError(RuntimeError):
    pass


def _read_stat(pid, proc_root="/proc"):
    """Return a PID identity; None means it vanished during the scan."""
    try:
        with open(os.path.join(proc_root, str(pid), "stat"), "rb") as stream:
            raw = stream.read()
    except FileNotFoundError:
        return None
    except OSError as error:
        raise TreeObservationError(f"cannot inspect /proc/{pid}/stat: {error}") from error
    close = raw.rfind(b")")
    if close < 0:
        raise TreeObservationError(f"malformed /proc/{pid}/stat for {pid}")
    fields = raw[close + 1:].split()
    try:
        # Remaining fields start at field 3 (state); ppid=field 4 and
        # starttime=field 22, hence offsets 1 and 19.
        return {"pid": pid, "state": fields[0].decode("ascii"),
                "ppid": int(fields[1]), "pgrp": int(fields[2]),
                "starttime": int(fields[19])}
    except (IndexError, ValueError, UnicodeDecodeError) as error:
        raise TreeObservationError(f"malformed /proc/{pid}/stat fields") from error


def _snapshot(proc_root="/proc"):
    try:
        names = os.listdir(proc_root)
    except OSError as error:
        raise TreeObservationError(f"cannot enumerate {proc_root}: {error}") from error
    rows = {}
    for name in names:
        if name.isdigit():
            row = _read_stat(int(name), proc_root)
            if row is not None:
                rows[row["pid"]] = row
    return rows


def _descendants(rows, root_pid, root_starttime):
    root = rows.get(root_pid)
    if root is not None and root["starttime"] != root_starttime:
        raise TreeObservationError("root PID identity changed (possible PID reuse)")
    children = {}
    for row in rows.values():
        children.setdefault(row["ppid"], []).append(row["pid"])
    found = {}
    todo = [root_pid]
    visited = set()
    while todo:
        parent = todo.pop()
        if parent in visited:
            raise TreeObservationError("cycle in /proc parent graph")
        visited.add(parent)
        for pid in children.get(parent, ()):
            row = rows[pid]
            found[pid] = row
            todo.append(pid)
    return found


def _prctl_get():
    libc = ctypes.CDLL(None, use_errno=True)
    value = ctypes.c_int()
    result = libc.prctl(PR_GET_CHILD_SUBREAPER, ctypes.byref(value), 0, 0, 0)
    if result != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code))
    return value.value


def _prctl_set(value):
    libc = ctypes.CDLL(None, use_errno=True)
    result = libc.prctl(PR_SET_CHILD_SUBREAPER, int(value), 0, 0, 0)
    if result != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code))


class SubreaperScope:
    """One serialized launch scope; unknown tree state never counts as empty."""
    def __init__(self, *, proc_root="/proc", settle_s=0.08, poll_s=0.005,
                 cleanup_timeout_s=3.0):
        self.proc_root = proc_root
        self.settle_s = settle_s
        self.poll_s = poll_s
        self.cleanup_timeout_s = cleanup_timeout_s
        self.supervisor_pid = os.getpid()
        self.previous_subreaper = None
        self.enabled = False
        self.root_pid = None
        self.root_starttime = None
        self.registration_error = None
        self._observed = {}
        self.finished = False

    def begin(self):
        if self.enabled or self.finished:
            raise RuntimeError("subreaper scope cannot be reused")
        rows = _snapshot(self.proc_root)
        supervisor = rows.get(self.supervisor_pid)
        if supervisor is None:
            raise TreeObservationError("cannot identify measurement supervisor in /proc")
        preexisting = _descendants(rows, self.supervisor_pid, supervisor["starttime"])
        if preexisting:
            raise RuntimeError("refusing subreaper scope with preexisting descendants")
        self.previous_subreaper = _prctl_get()
        _prctl_set(1)
        self.enabled = True
        return self

    def register_root(self, pid):
        if not self.enabled or self.root_pid is not None:
            raise RuntimeError("subreaper scope is not ready for a root process")
        self.root_pid = pid
        row = _read_stat(pid, self.proc_root)
        if row is None:
            self.registration_error = "launched root disappeared before identity capture"
            raise TreeObservationError(self.registration_error)
        self.root_starttime = row["starttime"]
        self._observed[pid] = dict(row)
        if row["ppid"] != self.supervisor_pid:
            self.registration_error = "launched root is not a direct child of supervisor"
            raise TreeObservationError(self.registration_error)
        return self.root_starttime

    def _reap_adopted(self, owned):
        """Reap only known direct-child identities; never wildcard-wait unknowns."""
        by_pid = {pid: row["starttime"] for pid, row in owned.items()}
        reaped = []
        for pid, starttime in by_pid.items():
            # Popen owns the launched root's wait status; only reap adopted
            # descendants here.
            if pid == self.root_pid:
                continue
            try:
                current = _read_stat(pid, self.proc_root)
                if current is None or current["starttime"] != starttime:
                    continue
                if current["ppid"] != self.supervisor_pid or current["state"] != "Z":
                    continue
                got, _ = os.waitpid(pid, os.WNOHANG)
                if got == pid:
                    reaped.append({"pid": pid, "starttime": starttime})
            except ChildProcessError:
                continue
        return reaped

    def _signal_owned(self, owned):
        signaled = []
        # Signal all current descendants by stable PID identity. Descendants may
        # escape groups/sessions; parent ancestry under the subreaper is key.
        for pid, row in sorted(owned.items(), key=lambda pair: pair[1]["ppid"] == self.supervisor_pid):
            current = _read_stat(pid, self.proc_root)
            if current is None:
                continue
            if current["starttime"] != row["starttime"]:
                raise TreeObservationError(f"PID identity changed before cleanup signal: {pid}")
            try:
                os.kill(pid, signal.SIGKILL)
                signaled.append({"pid": pid, "starttime": row["starttime"]})
            except ProcessLookupError:
                continue
            except PermissionError as error:
                raise TreeObservationError(f"cannot terminate owned PID {pid}: {error}") from error
        return signaled

    def finish(self):
        if self.finished:
            return self.result
        started = time.monotonic()
        result = {"method": "linux_prctl_subreaper_and_proc_parent_tree",
                  "status": "unknown", "remaining_processes": None,
                  "previous_subreaper": self.previous_subreaper,
                  "subreaper_enabled": self.enabled, "subreaper_restored": False,
                  "signaled_processes": [], "reaped_processes": [],
                  "observed_processes": []}
        if not self.enabled:
            result["error"] = "subreaper scope was not enabled"
            result["observed_wall_s"] = time.monotonic() - started
            self.result = result
            self.finished = True
            return result
        if self.registration_error is not None or (self.root_pid is not None and self.root_starttime is None):
            result["error"] = self.registration_error or "launched root identity was not captured"
            result["root_pid"] = self.root_pid
            result["observed_wall_s"] = time.monotonic() - started
            result["observed_processes"] = [self._observed[pid] for pid in sorted(self._observed)]
            self.result = result
            self.finished = True
            return result
        deadline = started + self.cleanup_timeout_s
        empty_since = None
        try:
            while time.monotonic() < deadline:
                rows = _snapshot(self.proc_root)
                owned = _descendants(rows, self.supervisor_pid,
                                     rows[self.supervisor_pid]["starttime"])
                # Root is expected to have been waited by Popen. If still alive,
                # kill only after verifying the captured identity.
                root = rows.get(self.root_pid) if self.root_pid is not None else None
                if root is not None:
                    if root["starttime"] != self.root_starttime:
                        raise TreeObservationError("root PID identity changed")
                    owned[self.root_pid] = root
                for pid, row in owned.items():
                    previous = self._observed.get(pid)
                    if previous is not None and previous["starttime"] != row["starttime"]:
                        raise TreeObservationError(f"PID identity changed during scope: {pid}")
                    self._observed[pid] = dict(row)
                if owned:
                    empty_since = None
                    result["signaled_processes"].extend(self._signal_owned(owned))
                    result["reaped_processes"].extend(self._reap_adopted(owned))
                else:
                    # Require stable emptiness over a short settling window.
                    if empty_since is None:
                        empty_since = time.monotonic()
                    elif time.monotonic() - empty_since >= self.settle_s:
                        result.update(status="confirmed_empty_after_cleanup",
                                      remaining_processes=[],
                                      observed_descendant_count=0)
                        break
                time.sleep(self.poll_s)
            if result["status"] != "confirmed_empty_after_cleanup":
                rows = _snapshot(self.proc_root)
                owned = _descendants(rows, self.supervisor_pid,
                                     rows[self.supervisor_pid]["starttime"])
                root = rows.get(self.root_pid) if self.root_pid is not None else None
                if root is not None:
                    if root["starttime"] != self.root_starttime:
                        raise TreeObservationError("root PID identity changed")
                    owned[self.root_pid] = root
                if owned:
                    result.update(status="live_processes",
                                  remaining_processes=[{"pid": pid, "starttime": row["starttime"],
                                                        "ppid": row["ppid"], "state": row["state"]}
                                                       for pid, row in sorted(owned.items())])
                else:
                    result.update(status="unknown_unconfirmed_empty",
                                  remaining_processes=None)
        except Exception as error:
            result.update(status="unknown", remaining_processes=None, error=repr(error))
        # Restore only when the process tree was conclusively empty. On failure
        # retain subreaper mode rather than risk orphaning a live descendant.
        if result["status"] == "confirmed_empty_after_cleanup":
            try:
                _prctl_set(self.previous_subreaper)
                result["subreaper_restored"] = True
            except Exception as error:
                result.update(status="unknown_restore_failed", remaining_processes=None,
                              restore_error=repr(error))
        result["observed_wall_s"] = time.monotonic() - started
        result["previous_subreaper"] = self.previous_subreaper
        result["observed_processes"] = [self._observed[pid]
                                         for pid in sorted(self._observed)]
        result["root_pid"] = self.root_pid
        result["root_starttime"] = self.root_starttime
        self.result = result
        self.finished = True
        return result
