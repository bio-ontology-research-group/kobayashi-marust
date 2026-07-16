#!/usr/bin/env python3
"""Executable synthetic tests for the process-tree watchdog.

Runs without pytest: `python3 oracle/ore/test_tree_watchdog.py` prints OK and
exits 0, or raises AssertionError. Linux-only (uses /proc, os.fork, cgroup
layout); on other platforms it prints SKIP and exits 0.

The regressions guarded here are the ORE production-sweep failures on the
fast-blowup giants (ore_ont_3524, ore_ont_15703):

  * a worker that leaves the process group (setsid) must still be counted, so
    the 20 GB cap is enforced over the whole tree, not one group;
  * /proc/<pid>/stat must parse even when `comm` holds spaces and parentheses;
  * a kernel OOM kill of the reasoner must read back as a memout, not an error;
  * the terminal row must be checkpointed to disk BEFORE the kill, so a
    whole-cgroup OOM kill of the supervisor cannot lose it;
  * the frozen runner must always emit exactly one terminal JSON row.
"""
import json
import os
import signal
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tree_watchdog as tw  # noqa: E402

RUNNER = os.path.abspath(
    os.path.join(HERE, "..", "..", "results", "benchmarks",
                 "2026-07-15-routing", "bench_one_matrix_frozen.py")
)

# A child that forks `forks` grandchildren, each allocating `mb` MB, optionally
# detaching into its own session (setsid) to escape the parent's process group,
# then holds so the watchdog can sample the tree. The parent allocates too.
CHILD_SRC = r"""
import os, sys, time
mb = int(sys.argv[1]); forks = int(sys.argv[2]); hold = float(sys.argv[3])
setsid = sys.argv[4] == '1'
kids = []
for _ in range(forks):
    pid = os.fork()
    if pid == 0:
        if setsid:
            os.setsid()
        buf = bytearray(mb * 1024 * 1024)
        for i in range(0, len(buf), 4096):
            buf[i] = 1
        time.sleep(hold)
        os._exit(0)
    kids.append(pid)
buf = bytearray(mb * 1024 * 1024)
for i in range(0, len(buf), 4096):
    buf[i] = 1
time.sleep(hold)
for pid in kids:
    try:
        os.waitpid(pid, 0)
    except OSError:
        pass
"""

# A child that ignores SIGTERM/SIGINT and spins forever; only SIGKILL stops it.
STUBBORN_SRC = r"""
import signal, time
signal.signal(signal.SIGTERM, signal.SIG_IGN)
signal.signal(signal.SIGINT, signal.SIG_IGN)
while True:
    time.sleep(0.05)
"""

MB = 1024 * 1024


def _spawn(src, *cli):
    return subprocess.Popen(
        [sys.executable, "-c", src, *[str(a) for a in cli]],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        preexec_fn=tw.child_preexec,
    )


# ---------------------------------------------------------------------------
# unit tests (no subprocess)
# ---------------------------------------------------------------------------

def test_parse_stat_robust_comm():
    with tempfile.TemporaryDirectory() as d:
        proc = os.path.join(d, "proc")
        pdir = os.path.join(proc, "4242")
        os.makedirs(pdir)
        # comm = "(ev il) )" - spaces AND parens, the case a naive split breaks
        # on. Layout: pid (comm) state ppid pgrp ... field24=rss(pages).
        fields_after_comm = ["S", "7", "99"] + ["0"] * 18 + ["512"] + ["0"] * 30
        with open(os.path.join(pdir, "stat"), "w") as fh:
            fh.write("4242 ((ev il) )) " + " ".join(fields_after_comm))
        ppid, pgrp, rss = tw.parse_proc_stat("4242", proc=proc)
        assert ppid == 7, ppid
        assert pgrp == 99, pgrp
        assert rss == 512 * tw.PAGE_SIZE, rss


def test_tree_and_group_rss_walk_and_union():
    # tree: 100 -> {200 -> 300}, and 400 is reparented (ppid 1) but shares pgid.
    snap = {
        100: (1, 100, 10),
        200: (100, 100, 20),
        300: (200, 999, 30),   # left the group via setsid, still a descendant
        400: (1, 100, 40),     # reparented to init, still in the group
        500: (1, 500, 50),     # unrelated
    }
    total, members = tw.tree_and_group_rss(100, 100, snap)
    assert members == {100, 200, 300, 400}, members
    assert total == 10 + 20 + 30 + 40, total
    assert 500 not in members


def test_cgroup_current_v2():
    with tempfile.TemporaryDirectory() as d:
        proc, sysfs = os.path.join(d, "proc"), os.path.join(d, "sys")
        os.makedirs(os.path.join(proc, "self"))
        with open(os.path.join(proc, "self", "cgroup"), "w") as fh:
            fh.write("0::/slurm/uid_1/job_2/step_0\n")
        cg = os.path.join(sysfs, "slurm/uid_1/job_2/step_0")
        os.makedirs(cg)
        with open(os.path.join(cg, "memory.current"), "w") as fh:
            fh.write("123456789\n")
        assert tw.cgroup_current_bytes(proc=proc, sysfs=sysfs) == 123456789


def test_cgroup_current_v1():
    with tempfile.TemporaryDirectory() as d:
        proc, sysfs = os.path.join(d, "proc"), os.path.join(d, "sys")
        os.makedirs(os.path.join(proc, "self"))
        with open(os.path.join(proc, "self", "cgroup"), "w") as fh:
            fh.write("5:memory:/slurm/job_9\n2:cpu:/slurm/job_9\n")
        cg = os.path.join(sysfs, "memory", "slurm/job_9")
        os.makedirs(cg)
        with open(os.path.join(cg, "memory.usage_in_bytes"), "w") as fh:
            fh.write("777\n")
        assert tw.cgroup_current_bytes(proc=proc, sysfs=sysfs) == 777


def test_cgroup_current_absent():
    with tempfile.TemporaryDirectory() as d:
        proc = os.path.join(d, "proc")
        os.makedirs(os.path.join(proc, "self"))
        with open(os.path.join(proc, "self", "cgroup"), "w") as fh:
            fh.write("0::/nowhere\n")
        assert tw.cgroup_current_bytes(proc=proc, sysfs=os.path.join(d, "sys")) is None


def test_classify_terminal():
    cap = 20 * 1024 * MB
    # a clean cap/timeout trip stands
    assert tw.classify_terminal("memout", True, -9, cap, cap, None) == "memout"
    assert tw.classify_terminal("timeout", True, -9, cap, cap, None) == "timeout"
    # unsolicited SIGKILL near the cap == kernel OOM took the reasoner -> memout
    assert tw.classify_terminal("ok", False, -signal.SIGKILL, int(0.95 * cap),
                                cap, None) == "memout"
    # unsolicited SIGKILL detected via cgroup accounting -> memout
    assert tw.classify_terminal("ok", False, -signal.SIGKILL, 0, cap,
                                int(0.98 * cap)) == "memout"
    # a small clean exit is left alone
    assert tw.classify_terminal("ok", False, 0, 5 * MB, cap, None) == "ok"
    # SIGKILL we sent (killed_by_us) with a low peak is not reclassified
    assert tw.classify_terminal("ok", True, -9, 5 * MB, cap, None) == "ok"


# ---------------------------------------------------------------------------
# integration tests (real subprocesses, real /proc measurement, real SIGKILL)
# ---------------------------------------------------------------------------

def test_memout_over_the_tree():
    # parent ~100 MB alone stays under the 180 MB cap; parent + one child does
    # not. A per-process cap would never trip; the tree cap must.
    trips = []
    proc = _spawn(CHILD_SRC, 100, 1, 3.0, 0)
    res = tw.monitor(proc, timeout=30, memcap_bytes=180 * MB,
                     sample_interval=0.01,
                     on_trip=lambda s, p: trips.append((s, p)))
    assert res.status == "memout", res.status
    assert res.killed_by_us
    assert res.peak_bytes > 180 * MB, res.peak_bytes
    assert trips and trips[0][0] == "memout"
    assert proc.poll() is not None


def test_tree_beats_group_setsid():
    # the child forks a grandchild that setsid()s out of the group before
    # allocating. The group-only poller would miss it; the tree walk must catch
    # it, so the tree still trips the cap.
    proc = _spawn(CHILD_SRC, 100, 1, 3.0, 1)
    res = tw.monitor(proc, timeout=30, memcap_bytes=180 * MB,
                     sample_interval=0.01)
    assert res.status == "memout", res.status
    # the escaped grandchild has a different pgid than the root child
    assert proc.poll() is not None


def test_timeout():
    proc = _spawn("import time\ntime.sleep(60)")
    start = time.monotonic()
    res = tw.monitor(proc, timeout=0.5, memcap_bytes=8 * 1024 * MB,
                     sample_interval=0.01)
    assert res.status == "timeout", res.status
    assert res.killed_by_us
    assert time.monotonic() - start < 20
    assert proc.poll() is not None


def test_stubborn_child_is_sigkilled():
    proc = _spawn(STUBBORN_SRC)
    res = tw.monitor(proc, timeout=0.5, memcap_bytes=8 * 1024 * MB,
                     sample_interval=0.01)
    assert res.status == "timeout", res.status
    assert proc.poll() is not None
    # SIGKILL, not the ignored SIGTERM, is what stopped it
    assert proc.returncode == -signal.SIGKILL, proc.returncode


def test_clean_small_run_is_ok():
    trips = []
    proc = _spawn("buf = bytearray(5 * 1024 * 1024)\n")
    res = tw.monitor(proc, timeout=30, memcap_bytes=512 * MB,
                     sample_interval=0.01,
                     on_trip=lambda s, p: trips.append(s))
    assert res.status == "ok", res.status
    assert not res.killed_by_us
    assert not trips
    assert proc.returncode == 0


def test_child_preexec_installs_address_space_backstop():
    proc = subprocess.run(
        ["sh", "-c", "ulimit -v"],
        capture_output=True,
        text=True,
        preexec_fn=lambda: tw.child_preexec(256 * MB),
        timeout=10,
    )
    assert proc.returncode == 0, proc
    assert int(proc.stdout.strip()) == 256 * 1024, proc.stdout


# ---------------------------------------------------------------------------
# end-to-end: the frozen runner always emits exactly one terminal row, and
# checkpoints it to disk before the kill.
# ---------------------------------------------------------------------------

FAKE_KM_SRC = """#!/usr/bin/env python3
import sys, time
# ignore argv (classify <ont>); balloon well past the cap and hold
buf = bytearray(400 * 1024 * 1024)
for i in range(0, len(buf), 4096):
    buf[i] = 1
time.sleep(5)
sys.stdout.write('{}')
"""


def test_runner_emits_one_memout_row_and_checkpoint():
    if not os.path.exists(RUNNER):
        print("SKIP runner missing")
        return
    with tempfile.TemporaryDirectory() as d:
        fake = os.path.join(d, "fake_km")
        with open(fake, "w") as fh:
            fh.write(FAKE_KM_SRC)
        os.chmod(fake, 0o755)
        ont = os.path.join(d, "ore_ont_3524.owl")
        open(ont, "w").close()
        ckpt = os.path.join(d, "row.ckpt")
        work = os.path.join(d, "work")
        out = subprocess.run(
            [sys.executable, RUNNER,
             "--kind", "km", "--arm", "production_all",
             "--ontology", ont, "--binary", fake, "--binary-sha", "deadbeef",
             "--gold-kind", "none", "--workdir", work,
             "--checkpoint", ckpt,
             "--timeout", "60", "--memcap-mb", "200",
             "--env", "KM_ROUTE=production_all"],
            capture_output=True, text=True, timeout=120,
        )
        lines = [ln for ln in out.stdout.splitlines() if ln.strip()]
        assert len(lines) == 1, (out.stdout, out.stderr)
        row = json.loads(lines[0])
        assert row["ont"] == "ore_ont_3524.owl", row
        assert row["arm"] == "production_all"
        assert row["status"] == "memout", row
        assert row["binary_sha256"] == "deadbeef"
        assert row["peak_mb"] > 200, row["peak_mb"]
        # the durable checkpoint exists and carries the same terminal verdict,
        # so a whole-cgroup OOM kill of the supervisor could not have lost it
        assert os.path.exists(ckpt)
        crow = json.loads(open(ckpt).read())
        assert crow["ont"] == "ore_ont_3524.owl"
        assert crow["arm"] == "production_all"
        assert crow["status"] == "memout"
        assert crow["binary_sha256"] == "deadbeef"


def test_runner_adjudicates_hard_as_allocation_failure_as_memout():
    if not os.path.exists(RUNNER):
        print("SKIP runner missing")
        return
    with tempfile.TemporaryDirectory() as d:
        fake = os.path.join(d, "fake_km")
        with open(fake, "w") as fh:
            fh.write(FAKE_KM_SRC)
        os.chmod(fake, 0o755)
        ont = os.path.join(d, "ore_ont_15703.owl")
        open(ont, "w").close()
        ckpt = os.path.join(d, "row.ckpt")
        out = subprocess.run(
            [sys.executable, RUNNER,
             "--kind", "km", "--arm", "production_all",
             "--ontology", ont, "--binary", fake, "--binary-sha", "cafebabe",
             "--gold-kind", "none", "--workdir", os.path.join(d, "work"),
             "--checkpoint", ckpt, "--timeout", "60", "--memcap-mb", "512",
             "--hard-as-mb", "128", "--env", "KM_ROUTE=production_all"],
            capture_output=True, text=True, timeout=120,
        )
        lines = [ln for ln in out.stdout.splitlines() if ln.strip()]
        assert len(lines) == 1, (out.stdout, out.stderr)
        row = json.loads(lines[0])
        assert row["status"] == "memout", row
        assert row["verdict"] == "memout", row
        assert row["peak_mb"] < 512, row
        assert json.loads(open(ckpt).read())["status"] == "memout"


def main():
    if sys.platform != "linux":
        print("SKIP not linux")
        return
    tests = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in tests:
        fn()
        print(f"  ok {fn.__name__}")
    print("OK")


if __name__ == "__main__":
    main()
