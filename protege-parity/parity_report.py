#!/usr/bin/env python3
"""Aggregate ParityRun JSON files into PARITY.md.

  parity_report.py <json dir> <PARITY.md> [--census census-per-input.tsv]
                   [--adjudication adjudication.md] [--title TEXT]

A "cell" is one (OWLReasoner method, ontology) pair. Its kind comes from the
verdicts of all calls of that method on that ontology (calls marked "info",
such as reasoner name and version, are left out):

  differ          some call gave a different answer (content or node structure)
  km_unsupported  KM threw or timed out where HermiT answered (and nothing differed)
  hermit_failed   every call failed in HermiT (error or timeout)
  agree           otherwise (agreement, or both threw the same exception, or
                  HermiT failed on some calls and KM answered them)

Parity score: share of cells where KM agrees with HermiT, or HermiT fails and
KM answers. The strict score counts a difference in node structure only (same
entities, different grouping) as a difference; the lenient score does not.
"""
import argparse, csv, glob, json, os, statistics, sys
from collections import Counter, defaultdict

DIFF = {"differ_content", "differ_structure"}
OWL = "http://www.w3.org/2002/07/owl#"
TOPBOT = {OWL + n for n in ("Thing", "Nothing", "topObjectProperty", "bottomObjectProperty",
                            "topDataProperty", "bottomDataProperty")}
TOPBOT |= {"inv(" + x + ")" for x in TOPBOT}


def topbottom_only(c):
    """True when both reasoners answered and differ only by top or bottom entities."""
    h, k = c.get("hermit", {}), c.get("km", {})
    if h.get("status") != "ok" or k.get("status") != "ok":
        return False
    ha, ka = h["ans"], k["ans"]
    if ha["t"] not in ("node", "nodeset") or ka["t"] != ha["t"]:
        return False
    hf = {e for n in ha["nodes"] for e in n}
    kf = {e for n in ka["nodes"] for e in n}
    return bool(hf ^ kf) and (hf ^ kf) <= TOPBOT


def short(s):
    s = str(s)
    for sep in ("#", "/"):
        if sep in s:
            s = s.rsplit(sep, 1)[1] if not s.endswith(sep) else s
            break
    return s.rstrip(")")


def shorten_ids(text):
    out, tok = [], ""
    # shorten every IRI inside a string for display
    import re
    return re.sub(r"https?://[^\s,()<>\[\]\"']+", lambda m: short(m.group(0)), text)


def nodes_of(a):
    return {tuple(n) for n in a.get("nodes", [])}


def describe(c):
    """Minimal description of a differing call."""
    h, k = c["hermit"], c["km"]
    if h.get("status") != "ok" or k.get("status") != "ok":
        return f"HermiT {h.get('status')}{(' ' + h['exc']) if 'exc' in h else ''}; KM {k.get('status')}{(' ' + k['exc']) if 'exc' in k else ''}"
    ha, ka = h["ans"], k["ans"]
    t = ha["t"]
    if t in ("node", "nodeset"):
        hn, kn = nodes_of(ha), nodes_of(ka)
        hf = {e for n in hn for e in n}
        kf = {e for n in kn for e in n}
        if hf != kf:
            oh, ok = sorted(hf - kf), sorted(kf - hf)
            def lst(x):
                return ", ".join(short(e) for e in x[:6]) + (f" (+{len(x) - 6} more)" if len(x) > 6 else "")
            return f"only HermiT: {{{lst(oh)}}}; only KM: {{{lst(ok)}}}"
        oh = sorted(hn - kn)
        ok = sorted(kn - hn)
        fmt = lambda ns: "; ".join("{" + ", ".join(short(e) for e in n) + "}" for n in ns[:3])
        return f"same entities, different nodes. HermiT nodes: {fmt(oh)}. KM nodes: {fmt(ok)}"
    if t == "set":
        hs, ks = set(ha["items"]), set(ka["items"])
        return f"only HermiT: {sorted(map(short, hs - ks))[:6]}; only KM: {sorted(map(short, ks - hs))[:6]}"
    if t == "bool":
        return f"HermiT {ha['v']}; KM {ka['v']}"
    return f"HermiT {ha.get('v')}; KM {ka.get('v')}"


def cell_kind(verdicts, mode):
    """mode: strict, lenient (grouping-only differences agree), adjusted (also top/bottom-only
    differences agree). Verdicts for adjusted mode arrive as 'differ_topbottom'."""
    lenient = mode != "strict"
    vs = Counter(verdicts)
    if all(v == "hermit_timeout" for v in verdicts):
        return "hermit_timeout"
    diff = vs["differ_content"] + (0 if lenient else vs["differ_structure"])
    if mode == "adjusted":
        pass
    else:
        diff += vs["differ_topbottom"]
    if diff:
        return "differ"
    if vs["km_unsupported"] or vs["km_timeout"]:
        return "km_unsupported"
    good = vs["agree"] + vs["both_error_same"] + vs["differ_structure"] * (1 if lenient else 0)
    if mode == "adjusted":
        good += vs["differ_topbottom"]
    if good:
        return "agree"
    if vs["hermit_error"]:
        return "hermit_failed_km_ok"
    return "hermit_failed_km_fail"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("report")
    ap.add_argument("--census")
    ap.add_argument("--adjudication")
    ap.add_argument("--title", default="HermiT parity scoreboard")
    a = ap.parse_args()

    census = {}
    if a.census:
        for r in csv.DictReader(open(a.census), delimiter="\t"):
            census[r["ontology"]] = r
    runs = []
    for f in sorted(glob.glob(os.path.join(a.outdir, "*.json"))):
        try:
            runs.append((os.path.basename(f)[:-5], json.load(open(f))))
        except Exception as e:
            print("skip", f, e, file=sys.stderr)
    if not runs:
        sys.exit("no result files")

    # cells[(method, ont)] -> list of (call, verdict)
    cells = defaultdict(list)
    methods = []
    per_ont = {}
    diffs = defaultdict(list)       # (method, kind) -> [(ont, call)]
    unsup = defaultdict(list)       # (method, exc) -> [(ont, call)]
    phase_ms = {"hermit": defaultdict(list), "km": defaultdict(list)}
    verdict_total = Counter()
    for name, r in runs:
        for c in r["calls"]:
            v = c.get("verdict")
            if v in (None, "info"):
                continue
            m = c["method"]
            if m not in methods:
                methods.append(m)
            cells[(m, name)].append((c, v))
            verdict_total[v] += 1
            if v in DIFF:
                diffs[(m, v)].append((name, c))
            elif v in ("km_unsupported", "km_timeout"):
                exc = c["km"].get("exc") or c["km"].get("status")
                unsup[(m, exc)].append((name, c))
        for who in ("hermit", "km"):
            rs = r["reasoners"].get(who, {})
            for ph, ms in rs.get("phase_ms", {}).items():
                phase_ms[who][ph].append((name, ms))
    methods.sort()
    onts = [n for n, _ in runs]

    def table_counts(mode):
        per_method = {m: Counter() for m in methods}
        per_o = {n: Counter() for n in onts}
        for (m, n), lst in cells.items():
            vs = [("differ_topbottom" if (v in DIFF and topbottom_only(c)) else v) for c, v in lst]
            k = cell_kind(vs, mode)
            per_method[m][k] += 1
            per_o[n][k] += 1
        return per_method, per_o

    pm, po = table_counts("strict")
    pm_l, po_l = table_counts("lenient")
    pm_a, po_a = table_counts("adjusted")

    def score(cnt):
        tot = sum(cnt.values()) - cnt["hermit_timeout"]
        good = cnt["agree"] + cnt["hermit_failed_km_ok"]
        return good, tot

    allc, allc_l, allc_a = Counter(), Counter(), Counter()
    for m in methods:
        allc.update(pm[m])
        allc_l.update(pm_l[m])
        allc_a.update(pm_a[m])
    g, t = score(allc)
    gl, _ = score(allc_l)
    ga, _ = score(allc_a)

    L = []
    L.append(f"# {a.title}\n")
    L.append(f"Ontologies: {len(onts)}. Method-ontology cells where HermiT answered or failed: {t}"
             f" ({allc['hermit_timeout']} further cells left out because HermiT timed out or never reached them). "
             f"Reasoner calls compared: {sum(verdict_total.values())}.\n")
    L.append(f"**Parity score (strict): {100.0 * g / t:.1f}%** ({g} of {t} cells). "
             f"Lenient score, where a node grouping difference with the same entities does not count: "
             f"{100.0 * gl / t:.1f}% ({gl} of {t}). "
             f"Adjusted score, which also ignores differences that consist only of owl:Thing or owl:Nothing "
             f"(or the top and bottom properties) appearing in one answer and not the other: "
             f"{100.0 * ga / t:.1f}% ({ga} of {t}).\n")
    L.append("A cell is one OWLReasoner method on one ontology; it counts for KM when KM agrees with HermiT on every "
             "call of that method (HermiT errors that KM answers are not held against KM), or when HermiT fails on "
             "the whole cell and KM answers. Settings: HermiT 1.4.3.456 with `ignoreUnsupportedDatatypes = true`, "
             "KM plugin through the OWL API 4.5.29, `KM_THREADS=1`.\n")
    L.append("Call verdicts, all calls: " + ", ".join(f"{k} {v}" for k, v in sorted(verdict_total.items())) + ".\n")

    L.append("## Per method\n")
    L.append("Counts are ontologies. `strict` columns count node grouping differences as differences.\n")
    L.append("| Method | Agreed | Differed | of which only grouping | of which only top/bottom | KM unsupported | HermiT failed (KM answers) | Both failed | HermiT timeout (excluded) | Score |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for m in methods:
        c, cl, ca = pm[m], pm_l[m], pm_a[m]
        gd, tot = score(c)
        sc = f"{100.0 * gd / tot:.0f}%" if tot else "-"
        L.append(f"| `{m}` | {c['agree']} | {c['differ']} | {c['differ'] - cl['differ']} | {cl['differ'] - ca['differ']} "
                 f"| {c['km_unsupported']} | {c['hermit_failed_km_ok']} | {c['hermit_failed_km_fail']} "
                 f"| {c['hermit_timeout']} | {sc} |")
    L.append("")

    L.append("## Per ontology\n")
    L.append("| Ontology | Fragment | KB | Sig (C/OP/DP/I) | HermiT | KM | Cells ok / total | Differed | KM unsupported | Score |")
    L.append("|---|---|---:|---|---|---|---:|---:|---:|---:|")
    for name, r in runs:
        c = po[name]
        gd, tot = score(c)
        sg = r["signature"]
        cen = census.get(name, {})
        frag = cen.get("fragment", "")
        def st(w):
            x = r["reasoners"].get(w)
            if not x:
                return "-"
            s = x["end"]
            if x.get("create_status") not in (None, "ok"):
                s = "create " + x["create_status"]
            return f"{s}, {x['wall_ms'] / 1000:.0f}s, ok {x.get('calls_ok', 0)}/{x.get('calls_planned', 0)}"
        L.append(f"| {name} | {frag} | {r['bytes'] // 1024} | {sg.get('classes')}/{sg.get('object_properties')}/"
                 f"{sg.get('data_properties')}/{sg.get('individuals')} | {st('hermit')} | {st('km')} | {gd}/{tot} "
                 f"| {c['differ']} | {c['km_unsupported']} | {100.0 * gd / max(tot, 1):.0f}% |")
    L.append("")

    L.append("## Time per phase\n")
    L.append("Wall time summed over the calls of each phase, in seconds, over all ontologies (median per ontology in brackets). "
             "Creation includes HermiT's load or KM's constructor. KM classifies on its first query or precompute.\n")
    phases = ["create", "consistency", "precompute", "classes", "class_expr", "object_props", "data_props",
              "individuals", "property_values", "entailment", "disjoint", "meta"]
    L.append("| Phase | HermiT total | HermiT median | KM total | KM median |")
    L.append("|---|---:|---:|---:|---:|")
    for ph in phases:
        cols = []
        for who in ("hermit", "km"):
            xs = [ms for _, ms in phase_ms[who].get(ph, [])]
            if xs:
                cols += [f"{sum(xs) / 1000:.1f}", f"{statistics.median(xs) / 1000:.2f}"]
            else:
                cols += ["-", "-"]
        L.append(f"| {ph} | " + " | ".join(cols) + " |")
    L.append("")

    L.append("## KM unsupported or failing\n")
    L.append("Calls where HermiT answered and KM threw an exception or timed out. Grouped by method and exception.\n")
    L.append("| Method | KM outcome | Calls | Ontologies | Example (ontology: call, message) |")
    L.append("|---|---|---:|---:|---|")
    for (m, exc), lst in sorted(unsup.items(), key=lambda kv: -len(kv[1])):
        ex_o, ex_c = lst[0]
        msg = ex_c["km"].get("msg", "")
        L.append(f"| `{m}` | {exc} | {len(lst)} | {len({o for o, _ in lst})} | {ex_o}: `{shorten_ids(ex_c['id'])[:90]}` {shorten_ids(msg)[:110]} |")
    L.append("")

    L.append("## Top differences\n")
    L.append("Differences where both reasoners answered, grouped by method. Up to three examples each; the raw JSON in the output directory holds all of them. Adjudication by the OWL 2 direct semantics follows in the next sections.\n")
    for (m, v), lst in sorted(diffs.items(), key=lambda kv: -len(kv[1])):
        ont_n = len({o for o, _ in lst})
        L.append(f"### `{m}`, {v.replace('_', ' ')}: {len(lst)} calls on {ont_n} ontologies\n")
        seen_o = set()
        shown = 0
        for o, c in lst:
            if o in seen_o and len(seen_o) < ont_n:
                continue
            seen_o.add(o)
            L.append(f"- {o}: `{shorten_ids(c['id'])[:160]}`: {describe(c)[:400]}")
            shown += 1
            if shown >= 3:
                break
        L.append("")

    if a.adjudication and os.path.exists(a.adjudication):
        L.append(open(a.adjudication).read())
    else:
        L.append("## Adjudication\n\nNot yet written.\n")

    open(a.report, "w").write("\n".join(L) + "\n")
    print(f"score strict {100.0 * g / t:.1f}% lenient {100.0 * gl / t:.1f}% cells {t}")


if __name__ == "__main__":
    main()
