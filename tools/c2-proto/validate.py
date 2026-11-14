"""Validation driver (design section 6).

    python validate.py hand            # hand-written cases
    python validate.py random N SEED   # N random normal-form KBs

For every query (the KB itself, and for random KBs also the
satisfiability of each ordinary concept name through a fresh nominal):

* proc:  exhaustive realisation search with at most KMAX core elements;
* check: the hinted checker on the realisation the search returns;
* c2a:   for C2a inputs, the search restricted to cores of nominal
         elements only (design section 7) must agree with proc;
* bf:    brute-force finite models up to NMAX elements (SAT);
* hermit, km: external references.

Writes one JSON line per query to results-<mode>.jsonl in the scratch
directory and prints every disagreement.
"""

from __future__ import annotations

import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(__file__))

import signal  # noqa: E402

from bruteforce import find_model, has_model  # noqa: E402
from cert import check_cert, model_to_cert  # noqa: E402
from steer import SteerError, steer  # noqa: E402
from cases import CASES  # noqa: E402
from kb import KB, parse  # noqa: E402
from oracles import SCRATCH, hermit_batch, km_batch, ofn_path  # noqa: E402
from realise import check_realisation, search, show_hint  # noqa: E402

KMAX_EXTRA = int(os.environ.get("C2_KMAX_EXTRA", "2"))
NMAX = int(os.environ.get("C2_NMAX", "6"))
PROC_TIMEOUT = int(os.environ.get("C2_PROC_TIMEOUT", "60"))


class _Timeout(Exception):
    pass


def _alarm(*_):
    raise _Timeout()


signal.signal(signal.SIGALRM, _alarm)


def nominal_classes_upper(kb: KB) -> int:
    return max(1, len(kb.noms))


def run_proc(kb: KB):
    kmax = nominal_classes_upper(kb) + KMAX_EXTRA
    t0 = time.time()
    signal.alarm(PROC_TIMEOUT)
    try:
        hint = search(kb, kmax)
    except _Timeout:
        return {"proc": None, "proc_s": PROC_TIMEOUT, "kmax": kmax}
    finally:
        signal.alarm(0)
    dt = time.time() - t0
    res = {"proc": hint is not None, "proc_s": round(dt, 3), "kmax": kmax}
    if hint is not None:
        res["core_size"] = len(hint[0])
        res["check"] = check_realisation(kb, hint)
        res["hint"] = show_hint(kb, hint)
    if kb.is_c2a():
        signal.alarm(PROC_TIMEOUT)
        try:
            h2 = search(kb, nominal_classes_upper(kb), extra_max=0 if kb.noms else 1)
            res["c2a"] = h2 is not None
            if h2 is not None:
                res["c2a_check"] = check_realisation(kb, h2)
        except _Timeout:
            res["c2a"] = None
        finally:
            signal.alarm(0)
    return res


def random_kb(rng: random.Random) -> KB:
    n_ord = rng.randint(2, 3)
    n_nom = rng.randint(1, 2)
    n = n_ord + n_nom
    m = 1 if rng.random() < 0.75 else 2
    noms = list(range(n_ord, n))
    R = lambda: rng.randrange(2 * m)  # noqa: E731
    cls = [("nom", a) for a in noms]
    ncl = rng.randint(3, 7)
    for _ in range(ncl):
        kind = rng.choices(["gci", "ex", "all", "ge", "le", "sub"],
                           weights=[3, 3, 1.5, 1, 3, 0.7 if m == 2 else 0])[0]
        a = rng.randrange(n)
        b = rng.randrange(n)
        if kind == "gci":
            body = tuple(sorted(set(rng.sample(range(n), rng.randint(0, 2)))))
            head = tuple(sorted(set(rng.sample(range(n), rng.randint(0, 2)))))
            if not body and not head:
                continue
            cls.append(("gci", body, head))
        elif kind == "ex":
            cls.append(("ex", a, R(), b))
        elif kind == "all":
            cls.append(("all", a, R(), b))
        elif kind == "ge":
            cls.append(("ge", a, rng.randint(1, 2), R(), b))
        elif kind == "le":
            cls.append(("le", a, rng.randint(0, 2), R(), b))
        elif kind == "sub":
            r1, r2 = R(), R()
            if r1 // 2 != r2 // 2:
                cls.append(("sub", r1, r2))
    # bias towards the interaction: a need towards a nominal and inverse counting at it
    if rng.random() < 0.7:
        o = rng.choice(noms)
        r = R()
        a1 = rng.randrange(n_ord)
        cls.append(("ex", a1, r, o))
        cls.append(("le", o, rng.randint(0, 2), r ^ 1, rng.randrange(n)))
        if rng.random() < 0.5:  # a second level: something needs an a1 element
            a2 = rng.randrange(n_ord)
            r2 = R()
            cls.append(("ex", a2, r2, a1))
            cls.append(("le", a1, rng.randint(1, 2), r2 ^ 1, rng.randrange(n)))
        if rng.random() < 0.5:  # several elements that need o
            src = rng.choice(noms + list(range(n_ord)))
            cls.append(("ge", src, 2, R(), rng.choice([a1, rng.randrange(n_ord)])))
    if n_nom == 2 and rng.random() < 0.5:
        cls.append(("gci", tuple(noms), ()))
    names = tuple(f"A{i}" for i in range(n_ord)) + tuple(f"N{i}" for i in range(n_nom))
    rn = tuple(f"r{i}" for i in range(m))
    return KB(n, m, tuple(cls), names, rn)


def _compute(item):
    j, kb = item
    row = run_proc(kb)
    row["bf"] = find_model(kb, NMAX)
    if row["bf"] is not None:
        _, (cext, rext) = has_model(kb, row["bf"], want_model=True)
        cert, prom = model_to_cert(kb, row["bf"], cext, rext)
        why = []
        row["cert"] = check_cert(kb, cert, why)
        row["cert_why"] = why
        row["cert_core"] = len(cert[0])
        row["cert_promotions"] = prom
        try:
            cert2, st = steer(kb, row["bf"], cext, rext)
            why2 = []
            row["steer"] = check_cert(kb, cert2, why2)
            row["steer_why"] = why2
            row["steer_stats"] = st
        except SteerError as e:
            row["steer"] = False
            row["steer_why"] = [str(e)]
    row["c2a_input"] = kb.is_c2a()
    row["ofn"] = ofn_path(kb)
    return j, row


def queries_for(kb: KB, with_sat: bool):
    qs = [("kb", kb)]
    if with_sat:
        for a in range(kb.n):
            if a not in kb.noms:
                qs.append((f"sat {kb.cname(a)}", kb.sat_query(a)))
    return qs


def main():
    mode = sys.argv[1]
    rows = []
    if mode == "hand":
        only = os.environ.get("C2_ONLY")
        items = [(name, parse(src), exp, note) for (name, src, exp, note) in CASES
                 if not only or any(name.startswith(p) for p in only.split(","))]
        for name, kb, exp, note in items:
            rows.append({"name": name, "query": "kb", "expected": exp, "note": note, "kb": kb})
    else:
        N = int(sys.argv[2])
        seed = int(sys.argv[3])
        rng = random.Random(seed)
        for i in range(N):
            kb = random_kb(rng)
            for qn, q in queries_for(kb, with_sat=True):
                rows.append({"name": f"rand{seed}-{i}", "query": qn, "kb": q})
    t0 = time.time()
    from multiprocessing import Pool
    work = [(j, r["kb"]) for j, r in enumerate(rows)]
    with Pool(int(os.environ.get("C2_JOBS", "16"))) as pool:
        for k, (j, res) in enumerate(pool.imap_unordered(_compute, work)):
            rows[j].update(res)
            if (k + 1) % 50 == 0:
                print(f"... {k + 1}/{len(rows)} queries, {time.time() - t0:.0f} s", flush=True)
    hv = hermit_batch([r["ofn"] for r in rows])
    use_km = (mode == "hand" or os.environ.get("C2_KM_ALL") == "1") and not os.environ.get("C2_NO_KM")
    kv = km_batch([r["ofn"] for r in rows]) if use_km else {}
    tag = os.environ.get("C2_TAG", "")
    out = os.path.join(SCRATCH, f"results-{mode}{'' if mode == 'hand' else '-' + sys.argv[3]}{tag}.jsonl")
    dis = 0
    with open(out, "w") as f:
        for r in rows:
            r["hermit"] = hv.get(r["ofn"])
            r["km"] = kv.get(r["ofn"])
            kb = r.pop("kb")
            r["text"] = kb.show()
            problems = []
            if r.get("check") is False:
                problems.append("hint from search fails the checker")
            if r.get("c2a_check") is False:
                problems.append("C2a hint fails the checker")
            if r.get("steer") is False:
                problems.append("steered construction fails: " + "; ".join(r["steer_why"]))
            if r.get("cert") is False:
                problems.append("certificate from the finite model fails: " + "; ".join(r["cert_why"]))
            if r["proc"] is None:
                problems.append("proc timeout")
            if r["bf"] is not None and r["proc"] is False:
                problems.append(f"finite model of size {r['bf']} but no realisation")
            if r["hermit"] in ("true", "false") and r["proc"] is not None \
                    and (r["hermit"] == "true") != r["proc"]:
                problems.append(f"proc {r['proc']} vs HermiT {r['hermit']}")
            if "expected" in r and r["hermit"] in ("true", "false") \
                    and r["expected"] != (r["hermit"] == "true"):
                problems.append(f"expected {r['expected']} vs HermiT {r['hermit']}")
            if r["hermit"] not in ("true", "false"):
                problems.append(f"HermiT {r['hermit']}")
            if r.get("c2a") is not None and r["proc"] is not None and r["c2a"] != r["proc"]:
                problems.append(f"C2a {r['c2a']} vs proc {r['proc']}")
            if r.get("km") in ("true", "false") and r["hermit"] in ("true", "false") \
                    and r["km"] != r["hermit"]:
                problems.append(f"km {r['km']} vs HermiT {r['hermit']}")
            if "expected" in r and r["proc"] is not None and r["expected"] != r["proc"]:
                problems.append(f"expected {r['expected']} vs proc {r['proc']}")
            r["problems"] = problems
            if problems:
                dis += 1
                print(f"!! {r['name']} [{r['query']}]: {'; '.join(problems)}")
                print("   " + r["text"].replace("\n", "\n   "))
                if "hint" in r:
                    print("   realisation:\n     " + r["hint"].replace("\n", "\n     "))
            f.write(json.dumps(r) + "\n")
    n = len(rows)
    sat = sum(1 for r in rows if r["proc"])
    tos = sum(1 for r in rows if r["proc"] is None)
    certs = sum(1 for r in rows if r.get("cert"))
    prom = sum(1 for r in rows if r.get("cert_promotions", 0) > 0)
    steer_ok = sum(1 for r in rows if r.get("steer"))
    steer_ni = sum(1 for r in rows if r.get("steer_stats", {}).get("ni", 0) > 0)
    c2a = sum(1 for r in rows if r["c2a_input"])
    big = sum(1 for r in rows if r.get("core_size", 0) > max(1, r["text"].count("nom ")))
    print(f"{n} queries: {sat} consistent by proc, {n - sat - tos} without realisation up to kmax, "
          f"{tos} proc timeouts; {certs} certificates from finite models check "
          f"({prom} needed NI promotions); steered construction: {steer_ok} certificates check "
          f"({steer_ni} with NI steps); "
          f"{c2a} C2a inputs; {big} needed a core larger than the nominal names; "
          f"{dis} with problems; results in {out}; {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
