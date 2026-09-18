#!/usr/bin/env python3
"""Robust process-tree watchdog for the ORE benchmark harness.

Why this exists
---------------
The benchmark runner measures a reasoner's peak memory by polling ``/proc`` and
kills it when a measured RSS cap (20 GB on the production sweep) is crossed. The
Slurm step is allocated a little more than the cap (``--mem=28G``) so the Python
supervisor and the Slurm step survive long enough to publish a terminal row.

Two failure modes broke that arrangement for the fast-blowup giants
(ore_ont_3524, ore_ont_15703):

1. The old loop sampled the reasoner *process group* every 40 ms and trusted the
   sample as the only signal. A giant can allocate several GB between two 40 ms
   samples, so real RSS can cross the 28 GB cgroup limit before the poller ever
   observes 20 GB. The kernel cgroup OOM-killer then fires, and under Slurm's
   ``memory.oom.group`` it kills the whole step - the Python supervisor
   included - so no memout row is ever emitted. The sweep then treats those
   ontologies as permanently unfinished.

2. Even when the reasoner (not the supervisor) is chosen by the OOM-killer, the
   old loop recorded the death as an ``error`` (rc = -9), not a ``memout``.

This module fixes both without giving the reasoner more than its measured cap:

* Measurement is over the full *process tree* (descendants by PPID) unioned with
  the process group, so a worker that calls ``setsid`` cannot hide from the cap.
  ``/proc/<pid>/stat`` is parsed robustly (the ``comm`` field may contain spaces
  and parentheses, which a naive ``.split()`` mis-indexes).

* The cgroup's own accounting (``memory.current`` on v2,
  ``memory.usage_in_bytes`` on v1) is read every tick as a race-free backstop.
  It reflects real kernel-charged usage of the entire step continuously, so the
  watchdog trips its own memout - slightly above the reasoner cap but far below
  the cgroup hard limit - before the kernel OOM-killer can. The reasoner still
  only ever gets its measured cap; the small headroom only covers the
  supervisor's own footprint.

* The supervisor lowers its own ``oom_score_adj`` and raises the reasoner's, so
  that in the non-group cgroup case the kernel prefers the reasoner as victim.

* A trip fires an ``on_trip`` callback *before* the kill, letting the caller
  checkpoint a terminal row to disk. Even if the supervisor is then killed, the
  row already exists.

The module has no third-party dependencies and never raises out of the monitor
loop: measurement errors degrade to "counted nothing this tick" so the loop
keeps running and always returns a terminal :class:`WatchResult`.
"""

import errno
import os
import resource
import signal
import time

PAGE_SIZE = os.sysconf("SC_PAGE_SIZE")


def parse_proc_stat(pid, proc="/proc"):
    """Return ``(ppid, pgrp, rss_bytes)`` for ``pid`` or ``None``.

    Robust against a ``comm`` (field 2) that contains spaces or parentheses:
    fields after ``comm`` are located relative to the final ``')'`` rather than
    by a positional split. Returns ``None`` on any read/parse error (the process
    may have exited between listing and reading).
    """
    try:
        with open(f"{proc}/{pid}/stat", "rb") as handle:
            data = handle.read()
    except OSError:
        return None
    try:
        text = data.decode("ascii", "replace")
        rparen = text.rfind(")")
        if rparen < 0:
            return None
        # Fields after comm, 1-indexed from field 3 (state). rest[0] == field 3.
        rest = text[rparen + 1:].split()
        # field 4 ppid -> rest[1]; field 5 pgrp -> rest[2]; field 24 rss -> rest[21]
        ppid = int(rest[1])
        pgrp = int(rest[2])
        rss_pages = int(rest[21])
    except (IndexError, ValueError):
        return None
    return ppid, pgrp, rss_pages * PAGE_SIZE


def snapshot_all(proc="/proc"):
    """One pass over ``/proc``: ``{pid: (ppid, pgrp, rss_bytes)}``."""
    snap = {}
    try:
        entries = os.listdir(proc)
    except OSError:
        return snap
    for entry in entries:
        if not entry.isdigit():
            continue
        pid = int(entry)
        info = parse_proc_stat(pid, proc=proc)
        if info is not None:
            snap[pid] = info
    return snap


def tree_and_group_rss(root_pid, root_pgid, snap):
    """Sum RSS over the process tree rooted at ``root_pid`` unioned with every
    process in group ``root_pgid``.

    Returns ``(rss_bytes, member_pids)``. The tree walk (descendants by PPID)
    catches workers that left the group via ``setsid``; the group union catches
    workers whose in-tree parent already exited (reparented to init but still in
    the group). Together they cover the realistic escape routes a multi-process
    reasoner can take.
    """
    children = {}
    for pid, (ppid, _pgrp, _rss) in snap.items():
        children.setdefault(ppid, []).append(pid)

    members = set()
    if root_pid in snap:
        stack = [root_pid]
        while stack:
            pid = stack.pop()
            if pid in members:
                continue
            members.add(pid)
            stack.extend(children.get(pid, ()))

    if root_pgid is not None:
        for pid, (_ppid, pgrp, _rss) in snap.items():
            if pgrp == root_pgid:
                members.add(pid)

    total = sum(snap[pid][2] for pid in members if pid in snap)
    return total, members


def _read_int_file(path):
    try:
        with open(path, "rb") as handle:
            return int(handle.read().strip())
    except (OSError, ValueError):
        return None


def cgroup_current_bytes(proc="/proc", sysfs="/sys/fs/cgroup"):
    """Current memory charged to *this process's* cgroup, or ``None``.

    Handles cgroup v2 (``memory.current``) and v1 (``memory.usage_in_bytes``).
    Best-effort: any missing file yields ``None`` and the caller falls back to
    the ``/proc`` tree sum alone.
    """
    try:
        with open(f"{proc}/self/cgroup", encoding="ascii", errors="replace") as handle:
            lines = handle.read().splitlines()
    except OSError:
        return None

    # cgroup v2: a single "0::<path>" line, unified hierarchy.
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) == 3 and parts[0] == "0" and parts[1] == "":
            rel = parts[2].lstrip("/")
            val = _read_int_file(os.path.join(sysfs, rel, "memory.current"))
            if val is not None:
                return val

    # cgroup v1: the controller list in field 2 contains "memory".
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        controllers = parts[1].split(",")
        if "memory" in controllers:
            rel = parts[2].lstrip("/")
            for base in (os.path.join(sysfs, "memory", rel),
                         os.path.join(sysfs, "memory")):
                val = _read_int_file(os.path.join(base, "memory.usage_in_bytes"))
                if val is not None:
                    return val
    return None


def _self_rss_bytes(proc="/proc"):
    info = parse_proc_stat("self", proc=proc)
    return info[2] if info else 0


def protect_supervisor(proc="/proc"):
    """Best-effort: make the calling process the last OOM-kill candidate.

    Lowering ``oom_score_adj`` below 0 needs privilege, so this may quietly do
    nothing; the reasoner-side bias in :func:`child_preexec` is what actually
    protects the supervisor when unprivileged.
    """
    try:
        with open(f"{proc}/self/oom_score_adj", "w") as handle:
            handle.write("-1000")
    except OSError:
        pass


def child_preexec(hard_as_bytes=None):
    """``preexec_fn`` for the reasoner: new session + first OOM victim.

    ``os.setsid`` makes the reasoner a session and group leader (so its pgid ==
    its pid and the whole worker tree shares one group). Raising
    ``oom_score_adj`` to the maximum is always allowed for an unprivileged
    process and biases the kernel to kill the reasoner tree, not the supervisor,
    in the non-group cgroup case.
    """
    os.setsid()
    if hard_as_bytes is not None:
        try:
            limit = int(hard_as_bytes)
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        except (OSError, ValueError):
            pass
    try:
        with open("/proc/self/oom_score_adj", "w") as handle:
            handle.write("1000")
    except OSError:
        pass


def kill_tree(pids):
    """SIGKILL every pid in ``pids`` (already-dead pids are ignored)."""
    for pid in pids:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError as exc:
            if exc.errno != errno.ESRCH:
                pass


def classify_terminal(loop_status, killed_by_us, returncode, peak_bytes,
                      memcap_bytes, cgroup_peak_bytes, oom_fraction=0.9):
    """Decide the terminal status after the child is reaped.

    ``loop_status`` is what the monitor loop concluded (``ok``/``timeout``/
    ``memout``). If the loop saw a clean cap/timeout trip that stands. Otherwise
    a child that died by an *unsolicited* SIGKILL while sitting near the cap is
    the kernel OOM-killer taking the reasoner, which is a ``memout``, not an
    ``error``.
    """
    if loop_status in ("timeout", "memout"):
        return loop_status
    if not killed_by_us and returncode == -signal.SIGKILL:
        near_cap = peak_bytes >= oom_fraction * memcap_bytes
        cgroup_near = (cgroup_peak_bytes is not None
                       and cgroup_peak_bytes >= oom_fraction * memcap_bytes)
        if near_cap or cgroup_near:
            return "memout"
    return loop_status


class WatchResult:
    """Terminal outcome of :func:`monitor`."""

    __slots__ = ("status", "peak_bytes", "cgroup_peak_bytes", "wall_s",
                 "killed_by_us", "returncode", "members")

    def __init__(self, status, peak_bytes, cgroup_peak_bytes, wall_s,
                 killed_by_us, returncode, members):
        self.status = status
        self.peak_bytes = peak_bytes
        self.cgroup_peak_bytes = cgroup_peak_bytes
        self.wall_s = wall_s
        self.killed_by_us = killed_by_us
        self.returncode = returncode
        self.members = members

    @property
    def peak_mb(self):
        return self.peak_bytes / 1024 / 1024


def monitor(proc, *, timeout, memcap_bytes, root_pgid=None,
            sample_interval=0.02, cgroup_headroom_bytes=None, on_trip=None,
            proc_fs="/proc", sysfs="/sys/fs/cgroup", now=time.monotonic):
    """Enforce ``timeout`` and ``memcap_bytes`` on the tree under ``proc``.

    ``proc`` is a live ``subprocess.Popen`` started with ``child_preexec`` (so
    its pgid == its pid). The loop samples the process tree plus group RSS and
    the cgroup's own accounting every ``sample_interval`` seconds. On the first
    limit crossing it calls ``on_trip(status, peak_bytes)`` (used by the caller
    to checkpoint a terminal row to disk) and then SIGKILLs the whole tree.

    The cgroup reading is a race-free backstop. To stay correct even when the
    cgroup is shared (the Slurm step cgroup holds only supervisor + reasoner,
    but a bare login shell shares a much larger cgroup), it tracks the *growth*
    of ``memory.current`` since the loop started, i.e. the reasoner's own
    allocation, not the ambient baseline. It trips a memout when that growth
    exceeds ``memcap_bytes + cgroup_headroom_bytes`` (default headroom: the
    supervisor's own RSS plus 512 MB), which stays well under the Slurm hard
    limit, so the watchdog kills the reasoner before the kernel OOM-killer can
    reach the supervisor. The reasoner is still only ever allowed its measured
    tree cap.

    Never raises: measurement failures count as zero for that tick. Returns a
    :class:`WatchResult`.
    """
    root_pid = proc.pid
    if root_pgid is None:
        try:
            root_pgid = os.getpgid(root_pid)
        except OSError:
            root_pgid = root_pid
    if cgroup_headroom_bytes is None:
        cgroup_headroom_bytes = _self_rss_bytes(proc_fs) + 512 * 1024 * 1024
    cgroup_cap = memcap_bytes + cgroup_headroom_bytes

    start = now()
    peak = 0
    cgroup_peak = 0
    cgroup_baseline = cgroup_current_bytes(proc=proc_fs, sysfs=sysfs)
    have_cgroup = False
    status = "ok"
    members = {root_pid}

    while proc.poll() is None:
        snap = snapshot_all(proc=proc_fs)
        try:
            rss, members = tree_and_group_rss(root_pid, root_pgid, snap)
        except Exception:  # noqa: BLE001 - measurement must never kill the loop
            rss, members = 0, members
        if rss > peak:
            peak = rss
        cur = cgroup_current_bytes(proc=proc_fs, sysfs=sysfs)
        if cur is not None:
            have_cgroup = True
            if cgroup_baseline is None:
                cgroup_baseline = cur
            growth = cur - cgroup_baseline
            if growth > cgroup_peak:
                cgroup_peak = growth

        elapsed = now() - start
        if elapsed > timeout:
            status = "timeout"
            break
        if peak > memcap_bytes:
            status = "memout"
            break
        if have_cgroup and cgroup_peak > cgroup_cap:
            # Race-free backstop: real usage is climbing toward the cgroup hard
            # limit faster than the tree sampler resolved it. Attribute the tree
            # RSS as the reported peak but stop the run as a memout now.
            status = "memout"
            break
        time.sleep(sample_interval)

    killed_by_us = False
    if status != "ok":
        if on_trip is not None:
            # Durably record the terminal row BEFORE the kill, so a subsequent
            # whole-cgroup OOM kill of the supervisor cannot lose it.
            try:
                on_trip(status, peak)
            except Exception:  # noqa: BLE001 - checkpoint must not abort the kill
                pass
        kill_tree(members)
        killed_by_us = True

    try:
        proc.wait(timeout=15)
    except Exception:  # noqa: BLE001 - subprocess.TimeoutExpired or reap error
        kill_tree(members)
        try:
            proc.wait(timeout=15)
        except Exception:  # noqa: BLE001
            pass

    # Final measurement pass (a late allocation may have peaked just before exit).
    snap = snapshot_all(proc=proc_fs)
    try:
        rss, _ = tree_and_group_rss(root_pid, root_pgid, snap)
        peak = max(peak, rss)
    except Exception:  # noqa: BLE001
        pass
    cur = cgroup_current_bytes(proc=proc_fs, sysfs=sysfs)
    if cur is not None and cgroup_baseline is not None:
        cgroup_peak = max(cgroup_peak, cur - cgroup_baseline)

    wall = now() - start
    returncode = proc.returncode
    final_status = classify_terminal(
        status, killed_by_us, returncode, peak, memcap_bytes,
        cgroup_peak if have_cgroup else None,
    )
    return WatchResult(
        status=final_status,
        peak_bytes=peak,
        cgroup_peak_bytes=cgroup_peak if have_cgroup else None,
        wall_s=wall,
        killed_by_us=killed_by_us,
        returncode=returncode,
        members=members,
    )
