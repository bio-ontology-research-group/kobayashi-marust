#!/usr/bin/env python3
"""OWL → classification bridge for the Protege plugin (and CLI use).

Reads an OWL functional-syntax (`.ofn`) ontology, runs the *real* normalisation
front-end (`frontend.ofn_to_clauses`, reusing moose's `normalise` + `augment`),
invokes the `kobayashi-marust` engine, and prints a compact JSON classification
of the **named** concepts on stdout:

    { "consistent": <bool>,
      "subsumptions": [ ["Sub","Super"], ... ],   # named atomic A ⊑ B (B != A)
      "unsatisfiable": [ "C", ... ] }

Normalisation-internal concepts (`Q_*`, `__*`, prefixed builtins) are filtered
out, so the result is in terms of the ontology's own class names.

Usage:  python3 owl_classify.py ontology.ofn
Env:    KM_ENGINE  path to the kobayashi-marust binary (else autodetected).
"""
from __future__ import annotations
import json, os, subprocess, sys, tempfile, threading, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import frontend  # noqa: E402  (parse/normalise/augment; locates moose itself)
import el_route  # noqa: E402  (EL++ fast path via moose's completion reasoner)

BOTTOM = {"Nothing", "owl:Nothing", "⊥"}


def engine_path() -> Path:
    env = os.environ.get("KM_ENGINE")
    if env:
        return Path(env)
    # engine/py/ -> engine/target/release/kobayashi-marust
    for name in ("kobayashi-marust", "sroiq-context-saturate"):
        p = HERE.parent / "target" / "release" / name
        if p.exists():
            return p
    raise FileNotFoundError(
        "kobayashi-marust binary not found; set KM_ENGINE or run "
        "`cargo build --release` in engine/."
    )


def short(n: str) -> str:
    # Collapse the engine-internal name back to its OWL local name. frontend
    # disambiguates distinct IRIs that share a fragment (sound reasoning), but
    # the classification output must use the bare local name to match the gold
    # comparison convention (ore_canon.localname). See frontend.local_name.
    #
    # local_name == _short_base(full IRI), which already implements the gold
    # ore_canon.localname convention exactly: everything after the last '#', or
    # (if there is no '#') after the last '/'. Crucially it keeps the whole
    # post-'#' fragment, including any embedded '/' or '://' — ORE surrogate
    # classes look like '…obo/_#_hasValue__http://…/SWO_0000394__http://…/SWO_0000023'
    # and gold keeps that full fragment. The old code did an extra
    # `.rsplit('/')`, truncating such fragments to their last path segment
    # ('C2/C3_facet_joint' -> 'C3_facet_joint'; the _hasValue surrogate ->
    # 'SWO_0000023'), which showed as spurious extra+missing vs gold (ore_ont_14499,
    # 8135). Return local_name unchanged so output matches the gold convention.
    return frontend.local_name(n)


def is_internal(n: str) -> bool:
    # A name backed by a real OWL IRI is a real class, even if its local name
    # happens to match a moose-internal prefix (e.g. a `Q_minus`/`Q_plus` class
    # in symbols.owl). Only un-IRI-backed names get the prefix heuristic.
    if frontend.is_named_iri(n):
        return False
    s = short(n)
    return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
            or s.startswith("def_") or (":" in s and s not in BOTTOM))


def ofn_bin() -> str:
    env = os.environ.get("KM_OFN_BIN")
    if env:
        return env
    return str(HERE.parent / "target" / "release" / "ofn")


def run_ofn(ofn_path: str) -> dict:
    """Run the Rust `ofn` normalisation frontend; returns its
    {clauses, iri_map, named, declared, el_rbox_safe} dict. Exit 3 means the
    ontology is out of the supported fragment (datatypes), mirroring
    frontend.OutOfFragment."""
    proc = subprocess.run([ofn_bin(), ofn_path], capture_output=True, text=True)
    if proc.returncode == 3:
        raise frontend.OutOfFragment(proc.stderr.strip() or "out of fragment")
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    return json.loads(proc.stdout)


def elc_bin() -> str:
    env = os.environ.get("KM_ELC_BIN")
    if env:
        return env
    return str(HERE.parent / "target" / "release" / "elc")


def run_ofn_split(ofn_path: str):
    """Run `ofn` in split mode: the (large) clause set goes to a temp file in
    the engine/elc stdin shape `{"clauses":[...]}`, and the small side data
    {iri_map, named, declared, el_rbox_safe} is returned as a dict. Returns
    (clauses_path, meta); the caller owns clauses_path and must unlink it. This
    keeps the clause set out of Python entirely — parsing+re-serialising it
    dominated the EL fast path on large ontologies. Exit 3 => out of fragment."""
    cfd, clauses_path = tempfile.mkstemp(suffix=".clauses.json")
    os.close(cfd)
    mfd, meta_path = tempfile.mkstemp(suffix=".meta.json")
    os.close(mfd)
    try:
        with open(clauses_path, "w") as cf:
            proc = subprocess.run([ofn_bin(), ofn_path, "--meta", meta_path],
                                  stdout=cf, stderr=subprocess.PIPE, text=True)
        if proc.returncode == 3:
            os.unlink(clauses_path)
            raise frontend.OutOfFragment(proc.stderr.strip() or "out of fragment")
        if proc.returncode != 0:
            os.unlink(clauses_path)
            raise RuntimeError(proc.stderr)
        with open(meta_path) as mf:
            meta = json.load(mf)
        return clauses_path, meta
    finally:
        if os.path.exists(meta_path):
            os.unlink(meta_path)


def run_reasoner_file(argv, clauses_path):
    """Run a reasoner binary (elc or the context engine) reading the clause set
    straight from `clauses_path` via stdin (no Python serialisation)."""
    with open(clauses_path) as f:
        return subprocess.run(argv, stdin=f, capture_output=True, text=True)


class _EngineResult:
    __slots__ = ("returncode", "stdout", "stderr", "oom", "timed_out")

    def __init__(self, returncode, stdout, stderr, oom, timed_out=False):
        self.returncode, self.stdout, self.stderr, self.oom = returncode, stdout, stderr, oom
        self.timed_out = timed_out


# Engine children currently alive (registered by `_run_engine`): the portfolio
# race kills them when the certified EL path wins, and the event stops any
# subsequent spawn (e.g. the adaptive retry) from starting a new one.
_LIVE_ENGINES = []
_RACE_WON = threading.Event()


def _resolve_residue(partial, clauses_path, clauses):
    """Complete a PARTIAL certified-elc answer (exit 4): the certificate
    determined every named subject except `partial["unresolved"]`; classify
    exactly those with the context engine (KM_QUERIES limits the root
    contexts) and merge. Sound and complete: the certified subjects are exact
    by the per-subject criterion, the residue by the engine."""
    names = partial.pop("unresolved", [])
    if not names:
        return partial
    os.environ["KM_QUERIES"] = ",".join(names)
    _RACE_WON.clear()
    try:
        proc = _run_engine_adaptive(clauses_path, clauses)
    finally:
        os.environ.pop("KM_QUERIES", None)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    eng = json.loads(proc.stdout)
    subs = partial.get("subsumptions", {})
    subs.update(eng.get("subsumptions", {}))
    partial["subsumptions"] = subs
    partial["inconsistent"] = bool(partial.get("inconsistent")) or bool(
        eng.get("inconsistent"))
    return partial


def _race_adaptive_vs_elc(clauses_path, clauses, elc_proc, elc_out_path):
    """Race `_run_engine_adaptive` (in a thread) against the already-started
    certified-elc process writing to `elc_out_path`. Both sides only ever
    produce sound AND complete answers (a failing certificate exits 3), so the
    first one wins and the loser is killed. The racing elc runs under its own
    RSS cap (`KM_ELC_PORT_MEM_GB`, default 8 GiB)."""
    cap_gb = float(os.environ.get("KM_ELC_PORT_MEM_GB", "8"))
    cap = int(cap_gb * (1 << 30))
    done = {}

    def run_cb():
        try:
            done["proc"] = _run_engine_adaptive(clauses_path, clauses)
        except BaseException as e:  # surfaced below if elc does not win
            done["exc"] = e

    th = threading.Thread(target=run_cb, daemon=True)
    th.start()
    # A PARTIAL certificate (elc exit 4) answers all but a small residue of
    # subjects.  The residue still needs the context engine, which can be as
    # expensive as the full classification (the shared TBox closure dominates)
    # — so the partial result spawns a THIRD racer (a query-restricted engine
    # run under the elc memory cap) instead of forfeiting the full engine's
    # progress.  First finisher wins: full engine alone, or partial + residue.
    partial = None
    tgt = {}
    tgt_thread = None
    elc_lost = False

    def run_targeted(names):
        try:
            tgt["proc"] = _run_engine(
                clauses_path, clauses, rss_cap_gb=cap_gb,
                extra_env={"KM_QUERIES": ",".join(names)})
        except BaseException as e:
            tgt["exc"] = e

    while True:
        rc = elc_proc.poll()
        if rc is not None and not elc_lost:
            if rc == 0:
                _RACE_WON.set()
                for p in list(_LIVE_ENGINES):
                    try:
                        p.kill()
                    except Exception:
                        pass
                with open(elc_out_path) as f:
                    return json.load(f)
            if rc == 4 and partial is None:
                with open(elc_out_path) as f:
                    partial = json.load(f)
                names = partial.pop("unresolved", [])
                if not names:
                    _RACE_WON.set()
                    for p in list(_LIVE_ENGINES):
                        try:
                            p.kill()
                        except Exception:
                            pass
                    return partial
                tgt_thread = threading.Thread(
                    target=run_targeted, args=(names,), daemon=True)
                tgt_thread.start()
                elc_lost = True  # elc itself is done; the racers continue
            elif rc != 4:
                elc_lost = True  # exit 3 / crash: the engine must answer

        if tgt_thread is not None and not tgt_thread.is_alive():
            proc2 = tgt.get("proc")
            if proc2 is not None and proc2.returncode == 0:
                _RACE_WON.set()
                for p in list(_LIVE_ENGINES):
                    try:
                        p.kill()
                    except Exception:
                        pass
                eng = json.loads(proc2.stdout)
                subs = partial.get("subsumptions", {})
                subs.update(eng.get("subsumptions", {}))
                partial["subsumptions"] = subs
                partial["inconsistent"] = bool(partial.get("inconsistent")) or bool(
                    eng.get("inconsistent"))
                return partial
            tgt_thread = None  # targeted failed; the full engine remains

        if not th.is_alive():
            break
        if rc is None:
            try:
                rss = int(open("/proc/%d/statm" % elc_proc.pid).read().split()[1]) * 4096
                if rss > cap:
                    elc_proc.kill()
            except Exception:
                pass
        time.sleep(0.1)
    try:
        elc_proc.kill()
    except Exception:
        pass
    # the full engine answered: stop a still-running targeted racer
    _RACE_WON.set()
    for p in list(_LIVE_ENGINES):
        try:
            p.kill()
        except Exception:
            pass
    if "exc" in done:
        raise done["exc"]
    proc = done["proc"]
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    return json.loads(proc.stdout)


def _run_engine(clauses_path, clauses, threads=None, rss_cap_gb=None, extra_env=None,
                time_cap_s=None, argv=None, nice=False):
    """Run the context engine on the clause set, optionally forcing a thread
    count (`KM_THREADS`) and/or an RSS watchdog (GiB). The watchdog polls the
    engine's resident set and kills *only the engine child* (leaving this driver
    alive to retry) when it exceeds the cap -- so the default parallel attempt,
    which on existential-blow-up ontologies re-derives the shared successor
    contexts per query chunk and multiplies memory, can be aborted and retried
    single-threaded instead of memouting the whole job. RSS (not virtual address
    space) is used so legitimate large parallel runs are not falsely tripped."""
    if _RACE_WON.is_set():
        # the portfolio's certified EL path already answered: do not spawn
        # (the racing adaptive thread may still be unwinding its retry logic)
        return _EngineResult(-9, "", "portfolio: certified EL path won", False, False)
    env = dict(os.environ)
    if threads is not None:
        env["KM_THREADS"] = str(threads)
    if extra_env:
        env.update(extra_env)
    argv = argv or [str(engine_path())]
    if nice:
        # the niced racer (plain-clause engine in the absorption portfolio) must
        # only consume cores the primary leaves idle, so it cannot slow the
        # primary's hard-case win; it still finishes the fast cliff cases.
        argv = ["nice", "-n", "19"] + argv
    stdin_f = open(clauses_path) if clauses_path is not None else subprocess.PIPE
    p = subprocess.Popen(argv, stdin=stdin_f if clauses_path is not None else subprocess.PIPE,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
    _LIVE_ENGINES.append(p)
    oom = {"hit": False}
    timed = {"hit": False}
    if rss_cap_gb is not None or time_cap_s is not None:
        cap = int(rss_cap_gb * (1 << 30)) if rss_cap_gb is not None else None
        deadline = (time.time() + time_cap_s) if time_cap_s is not None else None

        def monitor():
            # All rayon worker threads share one address space, so the process
            # RSS (statm field 2, in pages) covers the whole engine.
            while p.poll() is None:
                if cap is not None:
                    try:
                        rss = int(open("/proc/%d/statm" % p.pid).read().split()[1]) * 4096
                    except Exception:
                        break
                    if rss > cap:
                        oom["hit"] = True
                        try:
                            p.kill()
                        except Exception:
                            pass
                        break
                if deadline is not None and time.time() > deadline:
                    timed["hit"] = True
                    try:
                        p.kill()
                    except Exception:
                        pass
                    break
                time.sleep(0.1)

        threading.Thread(target=monitor, daemon=True).start()
    # When piping the clause set, let communicate() own the stdin write: a
    # separate writer thread closing p.stdin races communicate()'s flush of the
    # same pipe (`ValueError: I/O operation on closed file` on fast-exiting
    # engine runs, e.g. small probes).
    try:
        out, err = p.communicate(input=None if clauses_path is not None
                                 else json.dumps({"clauses": clauses}))
    except (BrokenPipeError, ValueError):
        # the engine died before draining stdin (watchdog kill or crash);
        # collect what it wrote
        out, err = p.communicate()
    finally:
        try:
            _LIVE_ENGINES.remove(p)
        except ValueError:
            pass
    if clauses_path is not None:
        stdin_f.close()
    return _EngineResult(p.returncode, out, err, oom["hit"], timed["hit"])


def _run_engine_adaptive(clauses_path, clauses, nice=False, threads=None):
    """Parallel attempt under an RSS+time watchdog; on overflow/timeout/failure,
    fall back to a single-threaded legacy (per-`f` pay-as-you-go) run.

    The first attempt uses the configured `KM_THREADS` (the harness sets it; if
    unset the engine picks `available_parallelism`), the default central
    expansion strategy, an `KM_PAR_MEM_GB` RSS cap (default 18 GiB, under the
    typical 20 GiB benchmark memcap) and a wall cap `KM_CENTRAL_TIME_CAP`
    (default 190 s, under the typical 240 s per-ontology timeout). The central
    strategy collapses the body-conjunction blow-up but can concentrate the
    head-disjunction blow-up in shared-core contexts -- a few disjunction-heavy
    ontologies that the legacy per-`f` strategy classifies in seconds blow up
    under it. The time cap (set above the slowest central-OK ontology, ~182 s on
    ORE) makes those abort with budget left for the legacy fallback, which then
    classifies them within the per-ontology timeout. Speed-bound ontologies
    finish on the first attempt and never reach the fallback. Disable with
    `KM_NO_RETRY=1`."""
    cap = os.environ.get("KM_PAR_MEM_GB")
    cap = float(cap) if cap else 18.0
    tcap = os.environ.get("KM_CENTRAL_TIME_CAP")
    tcap = float(tcap) if tcap else 190.0
    central_on = not os.environ.get("KM_NO_CENTRAL")
    # first attempt thread count: an explicit override (the absorption portfolio
    # gives the plain racer a small dedicated count) else the env KM_THREADS.
    first = str(threads) if threads is not None else os.environ.get("KM_THREADS")
    # Time-cap the first attempt only when the central strategy is active (so an
    # explicit KM_NO_CENTRAL run keeps the prior unbounded-time behaviour).
    proc = _run_engine(clauses_path, clauses, threads=first, rss_cap_gb=cap,
                       time_cap_s=(tcap if central_on else None), nice=nice)
    if (proc.oom or proc.timed_out or proc.returncode != 0) \
            and not os.environ.get("KM_NO_RETRY"):
        if central_on:
            # Central blew up (memory or time): the legacy per-`f` strategy is the
            # proven-complete fallback and classifies these in seconds. Run it
            # single-threaded (shares successor contexts -> low memory), uncapped
            # in time/memory (the remaining harness budget + external memcap bound
            # it).
            proc = _run_engine(clauses_path, clauses, threads=1, rss_cap_gb=None,
                               extra_env={"KM_NO_CENTRAL": "1"}, nice=nice)
        elif first != "1":
            # Explicit legacy run: keep the original single-threaded retry.
            proc = _run_engine(clauses_path, clauses, threads=1, rss_cap_gb=None, nice=nice)
    return proc


def _tableau_to_out(tout: dict) -> dict:
    """Convert the hypertableau `TOutput` (consistent flag, [A,B] subsumption
    pairs, unsatisfiable list) into the engine's `out` shape ({name: [supers]},
    inconsistent flag) so the shared output-mapping code handles it unchanged.
    Unsatisfiable classes are emitted as subsumed by ⊥ (the downstream
    BOTTOM-super check then records them)."""
    subs: dict = {}
    for pair in tout.get("subsumptions", []):
        a, b = pair[0], pair[1]
        subs.setdefault(a, []).append(b)
    for u in tout.get("unsatisfiable", []):
        subs.setdefault(u, []).append("owl:Nothing")
    return {"subsumptions": subs,
            "inconsistent": not tout.get("consistent", True),
            "dropped": 0}


def _spawn_tableau(clauses_path, clauses):
    """If this ontology is a live-disjunction, in-fragment (ALCH, no inverse /
    number / nominals, nothing dropped/fenced) case, start the label-caching
    hypertableau (`KM_TAB_CACHE`) as a racer and return `(proc, out_path)`, else
    `None`. The tableau is single-threaded and tiny in memory, so racing it next
    to the context engine costs ~one core and recovers the live-∀+⊔ family the
    engine times out on. Both procedures are sound + complete on this fragment, so
    the first to finish wins (see `_race_cb_vs_tableau`). Gated by `KM_TAB_RACE`."""
    if not os.environ.get("KM_TAB_RACE"):
        return None
    tab_bin = os.environ.get("KM_TAB_BIN")
    if not tab_bin or not os.path.exists(tab_bin):
        return None
    try:
        cl = clauses if clauses is not None else \
            json.load(open(clauses_path))["clauses"]
    except Exception:
        return None
    # skip giants (TInput build + cache path are for small/medium disjunctive
    # ontologies; the engine path owns the giants).
    max_cl = int(os.environ.get("KM_TAB_MAX_CLAUSES", "20000"))
    if len(cl) > max_cl:
        return None
    # no disjunctive head => deterministic => the engine handles it; adding the
    # tableau buys nothing.
    if not any(len(c.get("head", [])) >= 2 for c in cl):
        return None
    try:
        import cb_to_ht
        tin = cb_to_ht.convert(cl, None)
    except Exception:
        return None
    # only race when the TInput FAITHFULLY represents the ontology: anything
    # dropped/fenced or any inverse/number/nominal means the cache path could
    # answer an under-specified problem, so defer entirely to the engine.
    if tin.get("fenced") or tin.get("dropped") or tin.get("inverse") \
            or tin.get("number") or tin.get("nominals"):
        return None
    env = dict(os.environ)
    env["KM_TAB_CACHE"] = "1"
    env.setdefault("KM_TAB_ORD", "0")
    fd, out_path = tempfile.mkstemp(suffix=".tabrace.json")
    # Run the tableau at the lowest scheduling priority: it must consume only
    # cycles the engine leaves idle (the disjunctive hot path is largely
    # single-threaded, so cores sit idle), never preempting the engine and
    # tipping an ontology the engine would have finished over the wall cap.
    nice = ["nice", "-n", "19"] if os.environ.get("KM_TAB_RACE_NICE", "1") != "0" else []
    try:
        proc = subprocess.Popen(
            nice + [tab_bin], stdin=subprocess.PIPE, stdout=os.fdopen(fd, "w"),
            stderr=subprocess.DEVNULL, text=True, env=env)
    except Exception:
        try:
            os.close(fd)
        except Exception:
            pass
        if os.path.exists(out_path):
            os.unlink(out_path)
        return None

    def feed():
        try:
            json.dump(tin, proc.stdin)
            proc.stdin.close()
        except Exception:
            pass

    threading.Thread(target=feed, daemon=True).start()
    return (proc, out_path)


def _race_cb_vs_tableau(clauses_path, clauses):
    """Race `_run_engine_adaptive` against a LAZILY-spawned label-caching
    hypertableau. The race is engineered to *never* penalise the engine on the
    ontologies it already handles:

      * the engine starts first and keeps every core;
      * the tableau is built (clause read + `cb_to_ht.convert`) and spawned off the
        critical path in a background thread, and only after a grace delay
        (`KM_TAB_RACE_DELAY`, default 30 s). An ontology the engine finishes within
        the delay therefore pays ZERO tableau cost — no clause read, no conversion,
        no extra process;
      * once spawned, the tableau runs at `nice 19` (see `_spawn_tableau`), so it
        consumes only cycles the engine leaves idle and cannot slow it down.

    Both sides are sound + complete on the recognised fragment, so the first
    finisher wins and the loser is killed. Returns the engine-shaped `out` dict."""
    done: dict = {}

    def run_cb():
        try:
            done["proc"] = _run_engine_adaptive(clauses_path, clauses)
        except BaseException as e:  # surfaced below if the tableau does not win
            done["exc"] = e

    th = threading.Thread(target=run_cb, daemon=True)
    th.start()

    # Lazily build + spawn the tableau racer, off the engine's critical path.
    tab: dict = {}
    cancel = threading.Event()
    delay = float(os.environ.get("KM_TAB_RACE_DELAY", "30"))

    def prep():
        t0 = time.time()
        while time.time() - t0 < delay:
            if not th.is_alive() or cancel.is_set():
                return  # engine already finished: never spend a cycle on the tableau
            time.sleep(0.2)
        if not th.is_alive() or cancel.is_set():
            return
        r = _spawn_tableau(clauses_path, clauses)
        if r is None:
            return
        # if the engine won while we were converting/spawning, discard immediately
        # so a stray tableau cannot leak into the next ontology in the chunk.
        if cancel.is_set():
            try:
                r[0].kill()
            except Exception:
                pass
            if os.path.exists(r[1]):
                os.unlink(r[1])
            return
        tab["proc"], tab["out"] = r

    prep_th = threading.Thread(target=prep, daemon=True)
    prep_th.start()

    tab_proc = None
    tab_out = None
    try:
        while True:
            if tab_proc is None and "proc" in tab:
                tab_proc, tab_out = tab["proc"], tab["out"]
            if tab_proc is not None:
                rc = tab_proc.poll()
                if rc is not None:
                    won = None
                    if rc == 0:
                        try:
                            with open(tab_out) as f:
                                won = _tableau_to_out(json.load(f))
                        except Exception:
                            won = None
                    if won is not None:
                        _RACE_WON.set()
                        for p in list(_LIVE_ENGINES):
                            try:
                                p.kill()
                            except Exception:
                                pass
                        return won
                    tab_proc = None  # tableau failed/fenced: the engine must answer
            if not th.is_alive():
                break
            time.sleep(0.05)
    finally:
        # stop the prep thread and reap any tableau it spawned (now or racing us).
        cancel.set()
        prep_th.join(timeout=2.0)
        tp = tab.get("proc")
        if tp is not None:
            try:
                tp.kill()
            except Exception:
                pass
        to = tab.get("out") or tab_out
        if to and os.path.exists(to):
            os.unlink(to)
    if "exc" in done:
        raise done["exc"]
    proc = done["proc"]
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    return json.loads(proc.stdout)


def _ofn_clauses_file(ofn_path: str, absorb: bool):
    """Run `ofn` once with KM_ABSORB forced on/off and stream the clause set to a
    temp file (engine stdin shape). Returns the path (caller unlinks) or None on
    failure. Used by the absorption portfolio to obtain the *plain* clause set
    alongside the (primary) absorbed one."""
    env = dict(os.environ)
    env["KM_ABSORB"] = "1" if absorb else "0"
    fd, path = tempfile.mkstemp(suffix=".clauses.json")
    os.close(fd)
    try:
        with open(path, "w") as cf:
            proc = subprocess.run([ofn_bin(), ofn_path], stdout=cf,
                                  stderr=subprocess.DEVNULL, env=env)
        if proc.returncode != 0:
            os.unlink(path)
            return None
        return path
    except Exception:
        if os.path.exists(path):
            os.unlink(path)
        return None


def _race_absorbed_plain(ofn_path: str, absorbed_path):
    """Absorption portfolio (KM_ABSORB_PORTFOLIO), run SEQUENTIALLY to respect the
    job memcap. Absorption removes the unguarded excluded-middle disjunctions that
    recover the live-disjunction family, but on rare ontologies (a DOLCE-style
    covering+disjointness TBox, ore_ont_6246) the removed clauses perturb the
    engine into an ~18 GB blow-up that the *plain* clause set classifies in <1 s.
    A concurrent race is ruled out by memory: legitimate absorbed runs already use
    up to ~18 GB (ore_ont_12698, 16444), so a second engine alongside blows the
    20 GB cap. Instead:

      1. run the PLAIN clause set first under a short time probe
         (`KM_ABSORB_PROBE_S`, default 8 s) at full cores — it aims to catch the
         fast plain cliff cases (6246 is ~0.35 s on an idle compute node) cheaply,
         at low memory;
      2. if it does not finish in the probe window, discard it and run the
         ABSORBED set alone with the full time/RSS budget (it recovers the family).

    Only one engine is ever resident, so memory never doubles. Both clause sets
    are verdict-equal (absorption is equisatisfiable), so whichever answers is a
    sound + complete classification. Returns the engine `out`.

    CAVEAT (sweep 6524): the probe is wall-clock, so the plain win is node-load
    sensitive. 6246's plain run is sub-second on an idle node but pathologically
    slow under contention; when the probe lands on a busy node it misses, the
    absorbed blow-up is taken, and 6246 times out. So the portfolio recovered the
    +10 absorbed family gold-clean but did NOT save 6246 (net +9, not +11). Raise
    `KM_ABSORB_PROBE_S` to widen the plain window at the cost of delaying the
    genuinely absorbed-only onts; a cleaner fix is a cheap static plain/absorbed
    router instead of a wall-clock probe."""
    plain_path = _ofn_clauses_file(ofn_path, absorb=False)
    try:
        if plain_path is not None:
            probe = float(os.environ.get("KM_ABSORB_PROBE_S", "8"))
            cap = os.environ.get("KM_PAR_MEM_GB")
            cap = float(cap) if cap else 18.0
            # plain probe: single capped attempt (no adaptive retry — the probe is
            # only meant to catch the fast plain wins, e.g. the 6246 cliff).
            pp = _run_engine(plain_path, None, threads=os.environ.get("KM_THREADS"),
                             rss_cap_gb=cap, time_cap_s=probe)
            if pp.returncode == 0:
                return json.loads(pp.stdout)
        # plain absent or didn't finish fast: the absorbed set is the intended
        # winner, run it alone with the full budget.
        proc = _run_engine_adaptive(absorbed_path, None)
        if proc.returncode != 0:
            raise RuntimeError(proc.stderr)
        return json.loads(proc.stdout)
    finally:
        if plain_path is not None and os.path.exists(plain_path):
            os.unlink(plain_path)


def classify(ofn_path: str) -> dict:
    # Front-end: Rust `ofn` binary (fast; env-gated) or the Python normaliser.
    # Both yield the same clause set plus the output-mapping data (full IRI of
    # each internal name, the set of IRI-backed names, RBox EL-safety). The Rust
    # path avoids the 45-100s Python parse+normalise on large ontologies.
    use_rust_el = bool(os.environ.get("KM_RUST_EL"))
    clauses_path = None  # set in the zero-copy path; clauses then stay out of Python
    clauses = None
    abox_inconsistent = False
    if os.environ.get("KM_RUST_FRONTEND"):
        if use_rust_el:
            # Zero-copy: ofn writes the clause set to a file and the small side
            # data to a meta file; Python reads only the meta. elc / the engine
            # read the clauses straight from the file (no parse+re-dump in Python).
            clauses_path, meta = run_ofn_split(ofn_path)
            _iri_map = meta["iri_map"]
            _named = set(meta["named"])
            rbox_safe = bool(meta["el_rbox_safe"])
            abox_inconsistent = bool(meta.get("abox_inconsistent"))
            asserted_classes = set(meta.get("asserted_classes") or [])
        else:
            data = run_ofn(ofn_path)
            clauses = data["clauses"]
            _iri_map = data["iri_map"]
            _named = set(data["named"])
            rbox_safe = bool(data["el_rbox_safe"])
            abox_inconsistent = bool(data.get("abox_inconsistent"))
            asserted_classes = set(data.get("asserted_classes") or [])
        full_iri = lambda n: _iri_map.get(n, n)          # noqa: E731
        named_iri = lambda n: n in _named                # noqa: E731
    else:
        clauses = frontend.ofn_to_clauses(ofn_path)
        full_iri = frontend.full_iri
        named_iri = frontend.is_named_iri
        rbox_safe = el_route.rbox_el_safe(frontend.ofn_rbox(ofn_path))
        asserted_classes = set()

    # The Rust frontend proved the ABox forces an individual into two disjoint
    # named classes: the ontology is inconsistent. The CB engine drops ABox
    # clauses and would report it consistent, so short-circuit here (sound;
    # every such flag is a real OWL entailment). An inconsistent ontology has no
    # informative subsumptions, matching the gold reasoners' empty subsumption
    # set on these ontologies.
    if abox_inconsistent:
        if clauses_path is not None and os.path.exists(clauses_path):
            os.unlink(clauses_path)
        return {
            "consistent": False,
            "subsumptions": [],
            "unsatisfiable": [],
            "dropped": 0,
        }

    def is_internal(n: str) -> bool:
        # A name backed by a real OWL IRI is a real class even if its local name
        # matches a moose-internal prefix; only un-IRI-backed names get the
        # prefix heuristic. Uses the active frontend's IRI-backed-name predicate.
        if named_iri(n):
            return False
        s = short(n)
        return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
                or s.startswith("def_") or (":" in s and s not in BOTTOM))

    try:
        out = None
        # EL fast path: classify EL++ ontologies with the ELK-style completion.
        # Only attempt it when the RBox is EL-safe; otherwise go straight to the
        # context engine.
        if use_rust_el:
            # Compiled `elc` decides EL-membership itself (exit 3 => not EL, fall
            # through to the context engine); it replaces the Python completion on
            # the large EL ontologies whose Python saturation exceeds the budget.
            # `clauses` is None here (the clause set lives only in the file), so
            # the Python el_route path must NOT be taken.
            # KM_ELC_FORCE=1 attempts elc even when the RBox is not EL-safe:
            # the non-EL role clauses then land in elc's residual, where only a
            # passing completeness certificate (KM_ELC_CERT) lets it answer;
            # otherwise it exits 3 and the context engine runs as usual.
            proc = None
            portfolio_on = bool(clauses_path is not None
                                and os.environ.get("KM_ELC_PORTFOLIO"))
            if rbox_safe and not portfolio_on:
                proc = run_reasoner_file([elc_bin()], clauses_path)
            elif (not rbox_safe) and not portfolio_on \
                    and os.environ.get("KM_ELC_FORCE"):
                # Forced attempt on a non-EL-safe RBox: only a passing
                # completeness certificate (KM_ELC_CERT) lets elc answer, and a
                # FAILING attempt can be arbitrarily expensive (saturation +
                # repair on a non-EL clause set). Bound it by wall clock and
                # RSS; hitting either bound falls through to the context
                # engine exactly like exit 3.
                budget = float(os.environ.get("KM_ELC_FORCE_BUDGET_S", "100"))
                cap_gb = float(os.environ.get(
                    "KM_ELC_FORCE_MEM_GB", os.environ.get("KM_PAR_MEM_GB", "14")))
                proc = _run_engine(clauses_path, None, argv=[elc_bin()],
                                   rss_cap_gb=cap_gb, time_cap_s=budget)
                if proc.oom or proc.timed_out:
                    proc = None
            if proc is not None:
                if proc.returncode == 3:
                    out = None
                elif proc.returncode == 4:
                    out = _resolve_residue(
                        json.loads(proc.stdout), clauses_path, clauses)
                elif proc.returncode != 0:
                    raise RuntimeError(proc.stderr)
                else:
                    out = json.loads(proc.stdout)
        elif rbox_safe and el_route.is_el(clauses):
            out = el_route.classify(clauses)
        if out is None:
            # Portfolio (KM_ELC_PORTFOLIO=1): race the certified EL path
            # (elc with the canonical-model completeness certificate,
            # KM_ELC_CERT=2) against the context engine. Both produce sound
            # AND complete answers (a failing certificate exits 3 and only
            # the engine can win), so taking the first one preserves
            # correctness; the certified path recovers near-EL ontologies the
            # engine times out on without stealing any budget from the
            # engine. The elc side runs under its own RSS cap
            # (KM_ELC_PORT_MEM_GB, default 8 GiB) so the combined footprint
            # stays under the job memcap.
            elc_race = None
            elc_out_path = None
            # The race covers BOTH rbox-safe and unsafe ontologies: a
            # rbox-safe ontology with non-EL clauses needs the certificate
            # (the bare elc exits 3 on it), and a pure-EL one wins the race
            # immediately anyway.
            if use_rust_el and clauses_path is not None \
                    and os.environ.get("KM_ELC_PORTFOLIO"):
                elc_env = dict(os.environ)
                elc_env.setdefault("KM_ELC_CERT", "2")
                # output to a file: certified answers can be hundreds of MB,
                # which would deadlock an undrained pipe
                fd, elc_out_path = tempfile.mkstemp(suffix=".elcrace.json")
                elc_race = subprocess.Popen(
                    [str(elc_bin())], stdin=open(clauses_path),
                    stdout=os.fdopen(fd, "w"), stderr=subprocess.DEVNULL,
                    text=True, env=elc_env)
            try:
                if elc_race is None:
                    # Absorption portfolio: when KM_ABSORB is on, the primary
                    # clause set is absorbed; race it (full cores) against the
                    # plain clause set (niced) so the rare absorption blow-up
                    # (ore_ont_6246) is covered by the plain run. Needs the source
                    # ofn_path (zero-copy gives only the absorbed clause file).
                    if os.environ.get("KM_ABSORB_PORTFOLIO") \
                            and os.environ.get("KM_ABSORB", "0") != "0" \
                            and clauses_path is not None:
                        out = _race_absorbed_plain(ofn_path, clauses_path)
                    # race the context engine against the label-caching tableau on
                    # in-fragment live-disjunction ontologies. The tableau is
                    # spawned lazily/niced inside the racer, so this is free for
                    # ontologies the engine finishes quickly (no-op otherwise).
                    elif os.environ.get("KM_TAB_RACE"):
                        out = _race_cb_vs_tableau(clauses_path, clauses)
                    else:
                        proc = _run_engine_adaptive(clauses_path, clauses)
                        if proc.returncode != 0:
                            raise RuntimeError(proc.stderr)
                        out = json.loads(proc.stdout)
                else:
                    # leave one core to the (single-threaded) certificate
                    # racer: with the engine on all cores it gets starved and
                    # loses races it wins handily alone
                    if "KM_THREADS" not in os.environ:
                        os.environ["KM_THREADS"] = str(
                            max(1, (os.cpu_count() or 2) - 1))
                    out = _race_adaptive_vs_elc(
                        clauses_path, clauses, elc_race, elc_out_path)
            finally:
                if elc_out_path is not None and os.path.exists(elc_out_path):
                    os.unlink(elc_out_path)
    finally:
        if clauses_path is not None and os.path.exists(clauses_path):
            os.unlink(clauses_path)

    # Output uses the FULL IRI (frontend.full_iri); the comparison harness
    # applies ore_canon.localname once, exactly as it does for every other
    # reasoner. Filtering (is_internal) and the self-/bottom-subsumption checks
    # stay on the short local name. Emitting the short name here instead made the
    # harness localname-truncate fragments containing '/' (ore_ont_14499/8135).
    subs, unsat = [], []
    unsat_names = set()
    for a, sups in out["subsumptions"].items():
        if is_internal(a):
            continue
        sa = short(a)
        fa = full_iri(a)
        for s in sups:
            if short(s) in BOTTOM:
                if fa not in unsat:
                    unsat.append(fa)
                    unsat_names.add(a)
                    unsat_names.add(sa)
            elif not is_internal(s) and short(s) != sa:
                subs.append([fa, full_iri(s)])
    # An unsatisfiable class with a provable asserted member makes the whole
    # ontology inconsistent (a : C and C <= bottom). The engine drops the ABox,
    # so apply the rule here using the frontend's asserted-classes profile.
    if unsat_names & asserted_classes:
        return {
            "consistent": False,
            "subsumptions": [],
            "unsatisfiable": [],
            "dropped": out.get("dropped", 0),
        }
    return {
        "consistent": not out.get("inconsistent", False),
        "subsumptions": sorted(subs),
        "unsatisfiable": sorted(unsat),
        "dropped": out.get("dropped", 0),
    }


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    lines = "--lines" in sys.argv[1:]
    if len(args) != 1:
        print("usage: owl_classify.py [--lines] ontology.ofn", file=sys.stderr)
        sys.exit(2)
    try:
        res = classify(args[0])
    except frontend.OutOfFragment as e:
        # honest decline: the ontology is outside the supported fragment
        # (datatypes). Report unsupported rather than a partial classification.
        print(f"unsupported: {e}", file=sys.stderr)
        sys.exit(3)
    if lines:
        # Dependency-free line format for the Java/Protege plugin:
        out = [f"CONSISTENT {1 if res['consistent'] else 0}",
               f"DROPPED {res['dropped']}"]
        out += [f"SUB\t{a}\t{b}" for a, b in res["subsumptions"]]
        out += [f"UNSAT\t{c}" for c in res["unsatisfiable"]]
        print("\n".join(out))
    else:
        print(json.dumps(res))
