"""Bound watchdog sampling cost to the worker's kernel cgroup on Slurm.

A process inherits its cgroup across fork/exec/setsid. Enumerate all nested
cgroups as well, then keep the original ancestry/group RSS calculation. On an
unavailable/inaccessible scope or a PID-namespace mismatch, use the original
whole-/proc sampler. Final subreaper cleanup still scans the full process table.
"""
import os
from pathlib import Path
import tree_watchdog

class ScopedSnapshot:
    def __init__(self, root_pid, sysfs='/sys/fs/cgroup'):
        self.root_pid = root_pid
        self.sysfs = Path(sysfs)
        self.scoped_samples = 0
        self.fallback_samples = 0
        self.max_scope_pids = 0
        self.path = None

    def __call__(self, proc='/proc'):
        try:
            lines = (Path(proc)/str(self.root_pid)/'cgroup').read_text().splitlines()
            candidates = []
            for line in lines:
                hierarchy, controllers, relative = line.split(':', 2)
                # Namespace roots can contain '..'; never interpret them as
                # paths outside the supplied cgroup mount.
                if '..' in Path(relative).parts:
                    continue
                if hierarchy == '0' and controllers == '':
                    candidates.append(self.sysfs/relative.lstrip('/'))
                elif 'memory' in controllers.split(','):
                    candidates.append(self.sysfs/'memory'/relative.lstrip('/'))
            for scope in candidates:
                try:
                    if not (scope/'cgroup.procs').is_file():
                        continue
                    pids = set()
                    def raise_walk_error(error):
                        raise error
                    for directory, _, _ in os.walk(scope, onerror=raise_walk_error):
                        pids.update(int(s) for s in (Path(directory)/'cgroup.procs').read_text().split())
                    # Also catches host PID lists exposed to a different PID
                    # namespace: never report an empty sampled worker tree.
                    if self.root_pid not in pids:
                        continue
                    snap = {}
                    for pid in pids:
                        info = tree_watchdog.parse_proc_stat(pid, proc=proc)
                        if info is not None:
                            snap[pid] = info
                    if self.root_pid not in snap:
                        continue
                    self.path = str(scope)
                    self.scoped_samples += 1
                    self.max_scope_pids = max(self.max_scope_pids, len(pids))
                    return snap
                except (OSError, ValueError):
                    continue
        except (OSError, ValueError):
            pass
        self.fallback_samples += 1
        return tree_watchdog.snapshot_all(proc=proc)

    def summary(self):
        return dict(scoped_samples=self.scoped_samples,
                    fallback_samples=self.fallback_samples,
                    max_scope_pids=self.max_scope_pids, cgroup_path=self.path)
