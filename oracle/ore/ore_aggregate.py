#!/usr/bin/env python3
"""Aggregate the ORE DL+EL classification sweep: coverage, time/memory, and
correctness vs a gold reasoner (Konclude, cross-checked against HermiT).

Reads res_*.jsonl from the job dir + the per-run .sig.gz signatures, joins the
ORE metadata for per-ontology OWL profile, and writes a markdown report + CSVs.
"""
import csv
import glob
import gzip
import json
import os
import statistics as st
import sys

HOME = os.path.expanduser("~")
JOBDIR = os.path.join(HOME, "bench", "ore_jobs")
OUTDIR = os.path.join(HOME, "bench", "ore_out")
# KM was re-run on the audit-fixed binary; its records/sigs live separately and
# supersede the buggy KM entries from the main sweep.
OUTDIR_KM = os.path.join(HOME, "bench", "ore_out_kmfix")


def outdir_for(reasoner):
    return OUTDIR_KM if reasoner == "km" else OUTDIR
META = glob.glob(os.path.join(HOME, "ore2015", "pool_sample", "*", "classification", "metadata.csv"))
REASONERS = ["konclude", "hermit", "elk", "sequoia", "km"]
GOLD = "konclude"


def load_meta():
    m = {}
    for mf in META:
        with open(mf) as f:
            for row in csv.DictReader(f):
                fn = row.get("ore2015_filename")
                if not fn:
                    continue
                def num(k):
                    try:
                        return int(float(row.get(k) or 0))
                    except ValueError:
                        return 0
                m.setdefault(fn, {
                    "expr": row.get("expressivity", "?"),
                    "owl2_el": num("owl2_el"),
                    "tbox_nom": num("tbox_nominals"),
                    "abox_nom": num("abox_nominals"),
                    "dt": num("datatypes_count"),
                    "abox": num("abox_size"),
                    "axioms": num("logical_axiom_count"),
                    "classes": num("class_count"),
                })
    return m


def applicable(reasoner, meta):
    if reasoner in ("konclude", "hermit", "km"):
        return True            # full OWL 2 DL (km: compared empirically, flagged if incomplete)
    if reasoner == "elk":
        return meta.get("owl2_el", 0) == 1
    if reasoner == "sequoia":   # SRIQ: no nominals, no datatypes
        return meta.get("tbox_nom", 0) == 0 and meta.get("abox_nom", 0) == 0 and meta.get("dt", 0) == 0
    return False


UNSUPPORTED_PAT = ["does not support", "not supported", "unsupported", "not in the",
                   "ObjectOneOf", "DataProperty", "nominal", "outside the", "SRIQ",
                   "OWLProfileViolation", "ClassAssertion"]


def refine_status(rec):
    """error->unsupported when the FULL stderr shows an out-of-fragment rejection
    (the per-run record only stored a truncated tail)."""
    if rec.get("status") != "error":
        return rec["status"]
    p = os.path.join(outdir_for(rec["reasoner"]), f"{rec['reasoner']}__{rec['ont']}.err")
    try:
        with open(p, errors="replace") as f:
            low = f.read().lower()
    except OSError:
        return "error"
    return "unsupported" if any(pp.lower() in low for pp in UNSUPPORTED_PAT) else "error"


def load_records():
    recs = {}
    # main sweep (all reasoners) — but SKIP km (superseded by the fixed re-run)
    for rf in sorted(glob.glob(os.path.join(JOBDIR, "res_0*.jsonl"))):
        with open(rf) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if r["reasoner"] == "km":
                    continue
                r["status"] = refine_status(r)
                recs[(r["reasoner"], r["ont"])] = r
    # km from the audit-fixed re-run
    for rf in sorted(glob.glob(os.path.join(JOBDIR, "res_km_*.jsonl"))):
        with open(rf) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError:
                    continue
                r["status"] = refine_status(r)
                recs[(r["reasoner"], r["ont"])] = r
    return recs


def load_sig(reasoner, ont):
    p = os.path.join(outdir_for(reasoner), f"{reasoner}__{ont}.sig.gz")
    if not os.path.exists(p):
        return None
    with gzip.open(p, "rt") as f:
        txt = f.read()
    head, _, rest = txt.partition("\n")
    body, _, usect = rest.partition("\n#UNSAT\n")
    subs = set(tuple(l.split("\t")) for l in body.split("\n") if "\t" in l)
    unsat = set(l for l in usect.split("\n") if l)
    return head == "1", subs, unsat


def med(xs):
    return round(st.median(xs), 3) if xs else None


def main():
    meta = load_meta()
    recs = load_records()
    onts = sorted({o for (_, o) in recs})
    print(f"# ORE 2015 DL+EL classification benchmark\n")
    print(f"ontologies with >=1 result: {len(onts)}   total runs: {len(recs)}\n")

    # ---- coverage ----
    print("## Coverage (status counts over all attempted ontologies)\n")
    statuses = ["ok", "timeout", "memout", "unsupported", "error", "parse_error"]
    print("| reasoner | " + " | ".join(statuses) + " | applicable | ok/appl |")
    print("|" + "---|" * (len(statuses) + 3))
    for R in REASONERS:
        c = {s: 0 for s in statuses}
        appl = ok_appl = 0
        for o in onts:
            r = recs.get((R, o))
            if not r:
                continue
            c[r["status"]] = c.get(r["status"], 0) + 1
            if applicable(R, meta.get(o, {})):
                appl += 1
                if r["status"] == "ok":
                    ok_appl += 1
        print(f"| {R} | " + " | ".join(str(c[s]) for s in statuses) +
              f" | {appl} | {ok_appl} |")

    # ---- timing/memory on the common subset (all reasoners ok) ----
    common = [o for o in onts
              if all(recs.get((R, o), {}).get("status") == "ok" for R in REASONERS)]
    print(f"\n## Time & memory  (medians)\n")
    print(f"Common subset where *all five* succeeded: {len(common)} ontologies.\n")
    print("| reasoner | n_ok | median wall s | mean wall s | median peak MB | max peak MB | "
          "median wall (common) | median peak (common) |")
    print("|" + "---|" * 8)
    for R in REASONERS:
        ok = [recs[(R, o)] for o in onts if recs.get((R, o), {}).get("status") == "ok"]
        walls = [r["wall_s"] for r in ok]
        mems = [r["peak_mb"] for r in ok]
        cwalls = [recs[(R, o)]["wall_s"] for o in common]
        cmems = [recs[(R, o)]["peak_mb"] for o in common]
        print(f"| {R} | {len(ok)} | {med(walls)} | "
              f"{round(sum(walls)/len(walls),3) if walls else None} | {med(mems)} | "
              f"{round(max(mems),1) if mems else None} | {med(cwalls)} | {med(cmems)} |")

    # ---- correctness vs gold ----
    print(f"\n## Correctness vs {GOLD} (gold), on applicable ontologies where both succeeded & uncapped\n")
    print("| reasoner | compared | agree | incomplete (missing>0,extra=0) | unsound (extra>0) | both-disagree |")
    print("|" + "---|" * 6)
    gold_sigs = {}
    for o in onts:
        g = recs.get((GOLD, o))
        if g and g["status"] == "ok" and not g.get("capped"):
            gold_sigs[o] = g
    detail = {R: {"incomplete": [], "unsound": []} for R in REASONERS}
    for R in REASONERS:
        if R == GOLD:
            continue
        comp = agree = inc = uns = both = 0
        for o, g in gold_sigs.items():
            if not applicable(R, meta.get(o, {})):
                continue
            r = recs.get((R, o))
            if not r or r["status"] != "ok" or r.get("capped"):
                continue
            comp += 1
            if r.get("sig_sha") and r["sig_sha"] == g.get("sig_sha"):
                agree += 1
                continue
            sg = load_sig(GOLD, o)
            sr = load_sig(R, o)
            if not sg or not sr:
                continue
            missing = sg[1] - sr[1]
            extra = sr[1] - sg[1]
            if extra and missing:
                both += 1; detail[R]["unsound"].append(o)
            elif extra:
                uns += 1; detail[R]["unsound"].append(o)
            elif missing:
                inc += 1; detail[R]["incomplete"].append(o)
            else:
                # subs equal but unsat/consistency differ
                agree += 1
        print(f"| {R} | {comp} | {agree} | {inc} | {uns} | {both} |")

    # ---- gold sanity: hermit vs konclude ----
    hk_comp = hk_agree = 0
    disagreements = []
    for o in onts:
        k = recs.get(("konclude", o)); h = recs.get(("hermit", o))
        if k and h and k["status"] == "ok" and h["status"] == "ok" and not k.get("capped") and not h.get("capped"):
            hk_comp += 1
            if k.get("sig_sha") == h.get("sig_sha"):
                hk_agree += 1
            else:
                disagreements.append(o)
    print(f"\n## Gold sanity: HermiT vs Konclude\n")
    print(f"both ok & uncapped: {hk_comp};  identical classification: {hk_agree};  "
          f"differ: {len(disagreements)}")
    if disagreements:
        print("differing onts (investigate):", disagreements[:20])

    # dump detail + per-run csv
    with open(os.path.join(JOBDIR, "ore_detail.json"), "w") as f:
        json.dump({"common_n": len(common), "detail": detail,
                   "hk_disagree": disagreements}, f, indent=1)
    with open(os.path.join(JOBDIR, "ore_runs.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["reasoner", "ont", "expr", "owl2_el", "status", "wall_s", "peak_mb",
                    "n_sub", "n_unsat", "consistent", "capped", "host", "cores"])
        for (R, o), r in sorted(recs.items()):
            mm = meta.get(o, {})
            w.writerow([R, o, mm.get("expr"), mm.get("owl2_el"), r["status"], r["wall_s"],
                        r["peak_mb"], r.get("n_sub"), r.get("n_unsat"), r.get("consistent"),
                        r.get("capped"), r.get("host"), r.get("cores")])
    print(f"\nwrote {JOBDIR}/ore_runs.csv and ore_detail.json", file=sys.stderr)


if __name__ == "__main__":
    main()
