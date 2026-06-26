#!/usr/bin/env python3
"""Run ONE (router-mode, ontology) KM classification at a fixed budget, measure
wall + peak RSS of the whole process subtree (the /proc-poll over the spawned
process group, identical to the authoritative ore_runone.py so the JVM-vs-KM
numbers stay comparable), canonicalise, write a .sig.gz, and emit one JSON.

Router modes (KM_ROUTER_MODE):
  default : production routing (everything on)
  cb      : CB family only (engine + elc + absorb); tableau arms OFF
            (KM_NO_HT_RACE, KM_NO_HT_QO_ROUTER, KM_NO_HT_SHOQ)
  ht      : tableau-preferred race (KM_HT_MODE=race, QO + SHOQ on) so the
            ported hypertableau competes from t=0 against CB.

Uses the new pure-Rust `km classify` (self-reexecs all workers from ONE binary,
so we must NOT set KM_OFN_BIN/KM_ELC_BIN/KM_ENGINE/KM_TAB_BIN).

Usage: router_runone.py <ont_id>   (env: KM_ROUTER_MODE, OUTDIR, HT_TIMEOUT, KM_BIN)
"""
import sys, os, json, gzip, hashlib, signal, subprocess, time

HARN = "/home/hohndor/bench/ore_harness"
sys.path.insert(0, HARN)
from ore_canon import canonicalize

BENCH = "/home/hohndor/bench"
CORP = "/home/hohndor/ore2015/pool_sample/files"
KM = os.environ.get("KM_BIN", os.path.join(BENCH, "km", "km-router"))
MODE = os.environ.get("KM_ROUTER_MODE", "default")
OUTDIR = os.environ.get("OUTDIR", os.path.join(BENCH, "ore_out_router_%s" % MODE))
TIMEOUT = int(os.environ.get("HT_TIMEOUT", "120"))
MEMCAP_MB = int(os.environ.get("MEMCAP_MB", "20000"))


def mode_env(base):
    env = dict(base)
    # one fresh binary self-reexecs every worker: drop any sibling overrides.
    for k in ("KM_OFN_BIN", "KM_ELC_BIN", "KM_ENGINE", "KM_TAB_BIN",
              "KM_HT_MODE", "KM_NO_HT_RACE", "KM_NO_HT_QO_ROUTER",
              "KM_NO_HT_SHOQ", "KM_NO_ELC_PORTFOLIO", "KM_HT_QO_ROUTER",
              "KM_HT_SHOQ"):
        env.pop(k, None)
    env["KM_PAR_MEM_GB"] = env.get("KM_PAR_MEM_GB", "18")
    if MODE == "cb":
        env["KM_NO_HT_RACE"] = "1"
        env["KM_NO_HT_QO_ROUTER"] = "1"
        env["KM_NO_HT_SHOQ"] = "1"
    elif MODE == "ht":
        env["KM_HT_MODE"] = "race"
        env["KM_HT_QO_ROUTER"] = "1"
        env["KM_HT_SHOQ"] = "1"
    # default: leave production defaults untouched
    return env


def proc_group_rss(pgid, page):
    total = 0
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % d) as f:
                parts = f.read().split()
            if int(parts[4]) == pgid:
                total += int(parts[23]) * page
        except (OSError, IndexError, ValueError):
            continue
    return total


def main():
    o = sys.argv[1]
    # accept "ore_ont_X.owl", "ore_ont_X", or bare "X"
    o = o.strip()
    if o.endswith(".owl"):
        o = o[:-4]
    if o.startswith("ore_ont_"):
        o = o[len("ore_ont_"):]
    os.makedirs(OUTDIR, exist_ok=True)
    ontname = "ore_ont_%s.owl" % o
    owl = os.path.join(CORP, ontname)
    rec = {"ont": o, "mode": MODE, "host": os.uname().nodename}
    if not os.path.exists(owl):
        rec["status"] = "no_owl"; print(json.dumps(rec), flush=True); return

    tag = "km__%s" % ontname
    timefile = os.path.join(OUTDIR, tag + ".time")
    page = os.sysconf("SC_PAGE_SIZE")
    memcap = MEMCAP_MB * 1024 * 1024
    env = mode_env(os.environ)
    argv = ["/usr/bin/time", "-v", "-o", timefile, KM, "classify", owl]

    t0 = time.monotonic()
    p = subprocess.Popen(argv, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL, start_new_session=True)
    pgid = os.getpgid(p.pid)
    chunks = []
    import threading
    def drain(s=p.stdout, sink=chunks):
        try:
            for c in iter(lambda: s.read(65536), b""):
                sink.append(c)
        except Exception:
            pass
    rd = threading.Thread(target=drain, daemon=True); rd.start()
    peak = 0; status = "ok"
    while True:
        rc = p.poll()
        try:
            rss = proc_group_rss(pgid, page)
            if rss > peak:
                peak = rss
        except Exception:
            pass
        if rc is not None:
            break
        el = time.monotonic() - t0
        if el > TIMEOUT:
            status = "timeout"; break
        if peak > memcap:
            status = "memout"; break
        time.sleep(0.04)
    if status in ("timeout", "memout"):
        try: os.killpg(pgid, signal.SIGKILL)
        except OSError: pass
        try: p.wait(timeout=10)
        except Exception: pass
    wall = time.monotonic() - t0

    timev_rss = 0
    try:
        with open(timefile) as tf:
            for line in tf:
                if "Maximum resident set size" in line:
                    timev_rss = int(line.rsplit(":", 1)[1].strip()) * 1024; break
    except (OSError, ValueError):
        pass
    peak = max(peak, timev_rss)
    try: os.remove(timefile)
    except OSError: pass

    rec.update(status=status, wall_s=round(wall, 3),
               peak_mb=round(peak / 1024 / 1024, 1), rc=p.returncode)
    if status != "ok":
        print(json.dumps(rec), flush=True); return

    rd.join(timeout=15)
    text = b"".join(chunks).decode("utf-8", "replace")
    if p.returncode != 0 or not text.strip():
        rec["status"] = "error"; print(json.dumps(rec), flush=True); return
    try:
        cons, subs, unsat, capped = canonicalize(text, "json")
    except Exception as e:
        rec["status"] = "parse_error"; rec["err"] = repr(e)[:200]
        print(json.dumps(rec), flush=True); return
    sig = "\n".join("%s\t%s" % (a, b) for a, b in sorted(subs))
    usig = "\n".join(sorted(unsat))
    blob = (("1" if cons else "0") + "\n" + sig + "\n#UNSAT\n" + usig).encode()
    rec.update(consistent=cons, n_sub=len(subs), n_unsat=len(unsat),
               capped=capped, sig_sha=hashlib.sha256(blob).hexdigest())
    with gzip.open(os.path.join(OUTDIR, tag + ".sig.gz"), "wb") as gz:
        gz.write(blob)
    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
