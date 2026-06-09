#!/usr/bin/env python3
"""Run ONE (reasoner, ontology) classification, measure wall + peak RSS of the
whole process subtree, canonicalise the output, and emit a single JSON record.

Peak memory is measured by polling /proc for every process in the spawned
process group (start_new_session=True), so it captures JVM threads *and* the
KM python->rust child tree uniformly. Wall is monotonic. A watchdog enforces a
wall timeout and an RSS cap (kills the whole group).

Usage:
  ore_runone.py --reasoner konclude --ont /path/ore_ont_X.owl \
      --outdir ~/bench/ore_out --timeout 300 --memcap-mb 14000
"""
import argparse
import threading
import gzip
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ore_canon import canonicalize  # noqa: E402

HOME = os.path.expanduser("~")
# compute nodes have only Java 21; use the NFS-bundled Temurin JDK 8 so the JVM
# reasoners run under the same runtime everywhere (matching the validated runs).
JAVA = os.environ.get("BENCH_JAVA",
                      os.path.join(HOME, "bench", "jdk8dl", "jdk8u412-b08", "bin", "java"))
# Konclude needs libpcre.so.3 (PCRE1), absent on the nodes -> NFS-bundled copy.
LIBS = os.path.join(HOME, "bench", "reasoners", "libs")
BENCH = os.path.join(HOME, "bench")
KON = os.path.join(BENCH, "reasoners",
                   "Konclude-v0.7.0-1138-Linux-x64-GCC-Static-Qt5.12.10", "Binaries", "Konclude")
ELK = os.path.join(BENCH, "reasoners", "elk-distribution-cli-0.6.0", "elk.jar")
SEQ_DIST = os.path.join(HOME, "Sequoia", "reasoner-cli", "target", "universal",
                        "sequoia-command-line-interface-0.6.1-alpha")
KM_ENGINE = os.environ.get("KM_ENGINE_BIN", os.path.join(BENCH, "km", "kobayashi-marust-par"))
KM_PY = os.path.join(BENCH, "km", "py")
KM_PYTHONPATH = os.path.join(HOME, "sroiq-rerun", "pkg") + ":" + KM_PY
KM_PYBIN = os.path.join(HOME, "moose", ".venv", "bin", "python")

XMX = os.environ.get("BENCH_XMX", "-Xmx16g")

# unsupported-feature signatures (reasoner refuses the ontology, not a crash)
UNSUPPORTED_PAT = [
    "unsupported", "not supported", "is not in the", "not in the profile",
    "ObjectOneOf", "DataProperty", "nominal", "outside the", "SRIQ",
    "cannot handle", "OWLProfileViolation",
]


def build(reasoner, ont, outpath):
    """Return (argv, cwd, env, result_src) where result_src is ('stdout'|outpath)."""
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = LIBS + ":" + env.get("LD_LIBRARY_PATH", "")
    if reasoner == "konclude":
        return [KON, "classification", "-i", ont, "-o", outpath], None, env, outpath
    if reasoner == "elk":
        return [JAVA, XMX, "-jar", ELK, "-c", "-q", "-i", ont, "-o", outpath], None, env, outpath
    if reasoner == "sequoia":
        cp = os.path.join(SEQ_DIST, "lib", "*")
        return [JAVA, XMX, "-cp", cp, "com.sequoiareasoner.cli.Sequoia",
                "classify", "-o", outpath, ont], None, env, outpath
    if reasoner == "hermit":
        cp = ".:hermit_cp/*"
        return [JAVA, XMX, "-cp", cp, "Oracle", ont], BENCH, env, "stdout"
    if reasoner == "km":
        env["KM_ENGINE"] = KM_ENGINE
        env["PYTHONPATH"] = KM_PYTHONPATH
        env["KM_THREADS"] = env.get("KM_THREADS", "16")
        return [KM_PYBIN, os.path.join(KM_PY, "owl_classify.py"), ont], None, env, "stdout"
    raise ValueError(reasoner)


FMT = {"konclude": "owlxml", "elk": "functional", "sequoia": "functional",
       "hermit": "json", "km": "json"}


def proc_group_rss(pgid, page):
    total = 0
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open(f"/proc/{d}/stat") as f:
                parts = f.read().split()
            # field 5 (idx 4) pgrp; field 24 (idx 23) rss in pages
            if int(parts[4]) == pgid:
                total += int(parts[23]) * page
        except (OSError, IndexError, ValueError):
            continue
    return total


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--reasoner", required=True)
    ap.add_argument("--ont", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--timeout", type=int, default=300)
    ap.add_argument("--memcap-mb", type=int, default=14000)
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    ontname = os.path.basename(args.ont)
    tag = f"{args.reasoner}__{ontname}"
    taxout = os.path.join(args.outdir, tag + ".tax")
    page = os.sysconf("SC_PAGE_SIZE")
    memcap = args.memcap_mb * 1024 * 1024

    argv, cwd, env, src = build(args.reasoner, args.ont, taxout)
    timefile = os.path.join(args.outdir, tag + ".time")
    # /usr/bin/time -v gives authoritative single-process peak RSS (reliable even
    # for sub-100ms native binaries the poller would miss); the /proc poller adds
    # whole-subtree coverage (KM's python->rust child). Reported peak = max of both.
    argv = ["/usr/bin/time", "-v", "-o", timefile] + argv
    errf = open(os.path.join(args.outdir, tag + ".err"), "wb")
    outf = subprocess.PIPE if src == "stdout" else open(os.path.join(args.outdir, tag + ".out"), "wb")

    t0 = time.monotonic()
    p = subprocess.Popen(argv, cwd=cwd, env=env, stdout=outf, stderr=errf,
                         start_new_session=True)
    pgid = os.getpgid(p.pid)
    _stdout_chunks = []
    _reader = None
    if src == "stdout" and p.stdout is not None:
        def _drain(stream=p.stdout, sink=_stdout_chunks):
            try:
                for chunk in iter(lambda: stream.read(65536), b""):
                    sink.append(chunk)
            except Exception:
                pass
        _reader = threading.Thread(target=_drain, daemon=True)
        _reader.start()
    peak = 0
    status = "ok"
    stdout_data = b""
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
        if el > args.timeout:
            status = "timeout"
            break
        if peak > memcap:
            status = "memout"
            break
        time.sleep(0.04)

    if status in ("timeout", "memout"):
        try:
            os.killpg(pgid, signal.SIGKILL)
        except OSError:
            pass
        try:
            p.wait(timeout=10)
        except Exception:
            pass
    wall = time.monotonic() - t0

    # authoritative peak RSS from /usr/bin/time -v (kbytes), max'd with poller
    timev_rss = 0
    try:
        with open(timefile) as tf:
            for line in tf:
                if "Maximum resident set size" in line:
                    timev_rss = int(line.rsplit(":", 1)[1].strip()) * 1024
                    break
    except (OSError, ValueError):
        pass
    peak = max(peak, timev_rss)
    try:
        os.remove(timefile)
    except OSError:
        pass

    if src == "stdout":
        if _reader is not None:
            _reader.join(timeout=15)
        stdout_data = b"".join(_stdout_chunks)
    errf.close()
    if outf not in (subprocess.PIPE,):
        try:
            outf.close()
        except Exception:
            pass
    rc = p.returncode

    rec = {"reasoner": args.reasoner, "ont": ontname, "status": status,
           "wall_s": round(wall, 4), "peak_mb": round(peak / 1024 / 1024, 1),
           "rc": rc, "consistent": None, "n_sub": None, "n_unsat": None,
           "capped": False, "sig_sha": None,
           "host": os.uname().nodename, "cores": os.cpu_count()}

    if status == "ok":
        # gather reasoner output text
        if src == "stdout":
            text = stdout_data.decode("utf-8", "replace")
        else:
            try:
                with open(taxout, "r", errors="replace") as f:
                    text = f.read()
            except OSError:
                text = ""
        # classify failure vs unsupported
        try:
            with open(os.path.join(args.outdir, tag + ".err"), "r", errors="replace") as f:
                errtail = f.read()[-4000:]
        except OSError:
            errtail = ""
        if rc != 0 or not text.strip():
            low = errtail.lower()
            status = "unsupported" if any(pp.lower() in low for pp in UNSUPPORTED_PAT) else "error"
            rec["status"] = status
            rec["err_tail"] = errtail[-500:]
        else:
            try:
                cons, subs, unsat, capped = canonicalize(text, FMT[args.reasoner])
                sig = "\n".join(f"{a}\t{b}" for a, b in sorted(subs))
                usig = "\n".join(sorted(unsat))
                blob = (("1" if cons else "0") + "\n" + sig + "\n#UNSAT\n" + usig).encode()
                sha = hashlib.sha256(blob).hexdigest()
                with gzip.open(os.path.join(args.outdir, tag + ".sig.gz"), "wb") as gz:
                    gz.write(blob)
                rec.update(consistent=cons, n_sub=len(subs), n_unsat=len(unsat),
                           capped=capped, sig_sha=sha)
            except Exception as e:  # noqa: BLE001
                rec["status"] = "parse_error"
                rec["err_tail"] = repr(e)[:500]

    # clean the big taxonomy file to save space (sig.gz is the kept artifact)
    try:
        if os.path.exists(taxout):
            os.remove(taxout)
        op = os.path.join(args.outdir, tag + ".out")
        if os.path.exists(op):
            os.remove(op)
    except OSError:
        pass

    print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
