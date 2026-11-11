#!/usr/bin/env python3
"""Ibex certification driver for KM v1.6.0 (gates and full Rust suite).

Reproduces, on an Ibex batch node, what `capture-gate.py`, `run-five-gates.sh`
and `run-full-rust.py` do on ws, with the bindings that matter for exactness:

- the source is a clone of the tag at a fixed commit; before and after every
  step the commit and a clean `git status` are checked, and a manifest of every
  tracked file (Git blob sha256 and mode) is computed once and recomputed after
  each step;
- the five Lean gates run the repository's own gate scripts
  (`lean/run-<gate>-certification-gate.sh`), which build the Lean modules,
  audit the theorem surfaces, reject any `sorryAx`, and run their Rust
  integration tests; a gate passes only with exit 0 and zero `sorryAx` in its
  log;
- the full Rust suite is the CI recipe of `run-full-rust.py`: worker build,
  then `cargo test --release --lib` with the checker-bound tests of
  `.github/workflows/ci.yml` skipped (the gates ran them) and every integration
  target except the three the gates run, serially, `--test-threads=1`, in a
  cleaned environment (no `KM_*`, `CARGO_*`, `LEAN_*`, `RUST*` variables).

Usage: cert_ibex.py ROOT STEP   (STEP: gates | rust)
Receipts: ROOT/receipts/<step>.json; logs: ROOT/logs/cert-<step>-*.log.
"""
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
STEP = sys.argv[2]
SRC = ROOT / "src"
COMMIT = (ROOT / "COMMIT").read_text().strip()
HOME = Path.home()
RUST_TC = HOME / ".rustup/toolchains/1.95.0-x86_64-unknown-linux-gnu"
LEAN_TC = ROOT / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LOGS = ROOT / "logs"
RECEIPTS = ROOT / "receipts"
WORK = ROOT / "gate-work"
for d in (LOGS, RECEIPTS, WORK):
    d.mkdir(parents=True, exist_ok=True)


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()


def manifest():
    out = subprocess.check_output(["git", "ls-files", "-s"], cwd=SRC, text=True)
    files = {}
    for line in out.splitlines():
        meta, name = line.split("\t", 1)
        mode = meta.split()[0]
        p = SRC / name
        if p.is_symlink() or not p.is_file():
            files[name] = {"mode": mode, "sha256": None}
            continue
        files[name] = {"mode": mode, "sha256": sha(p),
                       "exec": bool(p.stat().st_mode & 0o111)}
    blob = json.dumps(files, sort_keys=True).encode()
    return hashlib.sha256(blob).hexdigest(), len(files)


def verify_source():
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=SRC, text=True).strip()
    dirty = subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                    cwd=SRC, text=True).strip()
    return head == COMMIT and not dirty, head, dirty


def base_env():
    env = {k: v for k, v in os.environ.items()
           if not k.startswith(("KM_", "CARGO_", "GIT_", "LEAN_", "RUST", "LLVM_PROFILE"))
           and k not in ("LD_PRELOAD", "LD_LIBRARY_PATH")}
    env.update(PATH=f"{RUST_TC}/bin:{LEAN_TC}/bin:{HOME}/.cargo/bin:" + env.get("PATH", ""),
               CARGO_HOME=str(HOME / ".cargo"), RUSTUP_HOME=str(HOME / ".rustup"),
               RUSTUP_TOOLCHAIN="1.95.0-x86_64-unknown-linux-gnu",
               CARGO_INCREMENTAL="0", CARGO_NET_OFFLINE="true")
    return env


def run(cmd, log, env, cwd):
    t = time.monotonic()
    with open(log, "wb") as f:
        code = subprocess.call(cmd, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    text = Path(log).read_text(errors="replace")
    counts = [tuple(map(int, x)) for x in
              re.findall(r"test result: .*? (\d+) passed; (\d+) failed; (\d+) ignored;", text)]
    return {"command": cmd, "log": str(log), "log_sha256": sha(log), "exit_code": code,
            "wall_s": round(time.monotonic() - t, 1),
            "counts": {"groups": len(counts), "passed": sum(c[0] for c in counts),
                       "failed": sum(c[1] for c in counts), "ignored": sum(c[2] for c in counts)},
            "sorryAx_in_log": text.count("sorryAx"),
            "failed_tests": re.findall(r"^test (\S+) \.\.\. FAILED", text, re.M)}


def receipt(name, body):
    p = RECEIPTS / f"{name}.json"
    p.write_text(json.dumps(body, indent=2) + "\n")
    print(json.dumps({"receipt": str(p), "status": body.get("status")}), flush=True)


ok, head, dirty = verify_source()
assert ok, (head, dirty)
mf_before, nfiles = manifest()
cpus = ",".join(map(str, sorted(os.sched_getaffinity(0))))
common = {"commit": COMMIT, "source_manifest_sha256": mf_before, "source_files": nfiles,
          "host": os.uname().nodename, "slurm_job": os.environ.get("SLURM_JOB_ID"),
          "cpus": cpus, "rustc": subprocess.check_output([f"{RUST_TC}/bin/rustc", "-V"], text=True).strip(),
          "lean": subprocess.check_output([f"{LEAN_TC}/bin/lean", "--version"], text=True).strip(),
          "driver_sha256": sha(__file__), "started_utc": now()}

if STEP == "gates":
    env = base_env()
    env.update(KM_WORK_ROOT=str(WORK), KM_CERT_LEAN_THREADS=os.environ.get("KM_CERT_LEAN_THREADS", "4"),
               KM_CERT_LEAN_CPUSET=cpus, KM_CERT_KEEP_NATIVE_CHECKERS="1", CARGO_BUILD_JOBS="8",
               KM_RULES_GATE_ORE_7278=str(ROOT / "inputs/ore_ont_7278.owl"))
    results = {}
    for gate in ["elc", "routing", "ht", "cb", "rules"]:
        script = SRC / f"lean/run-{gate}-certification-gate.sh"
        row = run(["bash", str(script)], LOGS / f"cert-gate-{gate}.log", env, SRC)
        same, h, d = verify_source()
        mf_after, _ = manifest()
        row.update(script_sha256=sha(script), source_unchanged_after=same and mf_after == mf_before,
                   status="passed" if row["exit_code"] == 0 and row["sorryAx_in_log"] == 0
                   and same and mf_after == mf_before else "rejected", ended_utc=now())
        results[gate] = row
        receipt(f"gate-{gate}", dict(common, gate=gate, **row))
    status = "passed" if all(r["status"] == "passed" for r in results.values()) else "rejected"
    receipt("gates", dict(common, status=status, gates={k: v["status"] for k, v in results.items()},
                          ended_utc=now()))

elif STEP == "rust":
    gates = json.loads((RECEIPTS / "gates.json").read_text())
    assert gates["status"] == "passed" and gates["commit"] == COMMIT, gates
    ci = (SRC / ".github/workflows/ci.yml").read_text()
    skips = re.search(r"checker_tests=\((.*?)\n\s*\)", ci, re.S).group(1).split()
    excluded = ["cb_live_state", "elc_certificate", "ht_taxonomy_certificate"]
    targets = sorted(p.stem for p in (SRC / "engine/tests").glob("*.rs") if p.stem not in excluded)
    env = base_env()
    env.update(CARGO_BUILD_JOBS="4", CARGO_TARGET_DIR=str(WORK / "target-rust"))
    workers = ["ofn", "elc", "kobayashi-marust", "tableau_cli"]
    cmds = [["cargo", "build", "--release", "--jobs", "4"] + sum((["--bin", n] for n in workers), [])]
    cmds += [["cargo", "test", "--release", "--jobs", "4", "--lib", "--", "--test-threads=1"]
             + sum((["--skip", n] for n in skips), [])]
    cmds += [["cargo", "test", "--release", "--jobs", "4", "--test", n, "--", "--test-threads=1"]
             for n in targets]
    rows = []
    for i, cmd in enumerate(cmds):
        row = run(cmd, LOGS / f"cert-rust-{i:03d}.log", env, SRC / "engine")
        rows.append(row)
        print(json.dumps({"i": i, "cmd": " ".join(cmd[:7]), "exit": row["exit_code"],
                          "counts": row["counts"]}), flush=True)
    same, h, d = verify_source()
    mf_after, _ = manifest()
    tot = {k: sum(r["counts"][k] for r in rows) for k in ["groups", "passed", "failed", "ignored"]}
    status = "passed" if all(r["exit_code"] == 0 for r in rows) and same and mf_after == mf_before else "failed"
    receipt("full-rust", dict(common, status=status, skipped_library_tests=skips,
                              excluded_integration_targets=excluded, integration_targets=targets,
                              cargo_commands=len(cmds), counts=tot, attempts=rows,
                              failed_tests=sum((r["failed_tests"] for r in rows), []),
                              source_unchanged_after=same and mf_after == mf_before, ended_utc=now()))
else:
    raise SystemExit(f"unknown step {STEP}")
