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
import argparse, csv, glob, json, os, re, statistics, sys
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


def arg_is_topbottom(call_id):
    return any(("owl#" + n) in call_id for n in ("Thing", "Nothing", "topObjectProperty", "bottomObjectProperty",
                                                  "topDataProperty", "bottomDataProperty"))


def arg_tag(call_id):
    """Which kind of argument the call had."""
    if arg_is_topbottom(call_id):
        return " (top/bottom argument)"
    inner = call_id[call_id.index("(") + 1:]
    if re.match(r"(Object|Data)[A-Za-z]+\(", inner) and not inner.startswith(("ObjectInverseOf",)):
        return " (anonymous class expression argument)"
    if inner.startswith("inv("):
        return " (inverse property argument)"
    return ""


def diff_kind(c):
    """A short label for the shape of a difference, used to group differences."""
    h, k = c["hermit"], c["km"]
    ha, ka = h["ans"], k["ans"]
    t = ha["t"]
    tb = arg_tag(c["id"])
    if t in ("node", "nodeset") and ka["t"] == t:
        hf = {e for n in ha["nodes"] for e in n}
        kf = {e for n in ka["nodes"] for e in n}
        if hf == kf:
            return "same entities, different node grouping"
        if (hf ^ kf) <= TOPBOT:
            return "only owl:Thing/owl:Nothing differ" + tb
        hr, kr = hf - TOPBOT, kf - TOPBOT
        if hr == kr:
            return "only owl:Thing/owl:Nothing differ" + tb
        if not kr:
            return "KM answers empty, HermiT does not" + tb
        if not hr:
            return "HermiT answers empty, KM does not" + tb
        if kr < hr:
            return "KM answer is a strict subset" + tb
        if hr < kr:
            return "KM answer is a strict superset" + tb
        return "answers overlap or are disjoint" + tb
    if t == "set" and ka["t"] == "set":
        hs, ks = set(ha["items"]), set(ka["items"])
        if not ks:
            return "KM answers empty, HermiT does not" + tb
        if not hs:
            return "HermiT answers empty, KM does not" + tb
        if ks < hs:
            return "KM answer is a strict subset" + tb
        if hs < ks:
            return "KM answer is a strict superset" + tb
        return "answers overlap or are disjoint" + tb
    if t == "bool":
        return f"HermiT {str(ha['v']).lower()}, KM {str(ka['v']).lower()}" + tb
    return "different values" + tb


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
    if vs["km_unsupported"]:
        return "km_unsupported"
    if vs["km_timeout"]:
        return "km_timeout"
    good = vs["agree"] + vs["both_error_same"] + vs["differ_structure"] * (1 if lenient else 0)
    if mode == "adjusted":
        good += vs["differ_topbottom"]
    if good:
        return "agree"
    if vs["hermit_error"]:
        return "hermit_failed_km_ok"
    return "hermit_failed_km_fail"


NOT_COVERED = """## What the harness does not cover

- Ontology edits. Every run loads the ontology once and queries it. `flush`, buffering, pending changes after an edit, incremental updates and the reasoner state after a failed run are not exercised (`getPending*` and `flush` are asked on an idle reasoner).
- Interruption and limits. `interrupt()` is only called idle or after a query ran past the per-call cap; progress monitor calls, `TimeOutException` from a configured timeout and Protégé's Stop button are not tested. The worker kill is the only hard limit.
- Configuration variants. One HermiT configuration (Protégé's, `ignoreUnsupportedDatatypes = true`), the default fresh entity policy and the default individual node set policy. `BY_SAME_AS`, `THROW_EXCEPTION` and the timeout are not varied.
- Protégé itself. No Protégé window, preference mapping, explanation workbench or DL Query tab. The harness checks the `OWLReasoner` answers those features read, not the features.
- Query shapes outside the plan: queries on anonymous individuals, data range class expressions with facets in `getInstances`, SWRL rules, keys, imports other than the W3C wine and food pair, and axioms the generator has no template for (keys, datatype definitions, annotation axioms beyond those in the ontology).
- Sampling. At most 200 entities per kind, 6 for the disjoint and different-individual queries, 30 property expressions for domains and ranges, 40 individuals by 15 properties for values, 5 axioms per axiom type. One seed (1). A difference outside the sample is not seen; the counts in the difference tables are counts of sampled calls, not of ontology facts.
- Correctness of HermiT. The harness is differential. Where both agree it does not know they are right; where they differ the adjudication section decides by hand on a sample, and not every shape has a source check.
- Scale and speed. Ontologies under 2 MB, one run per reasoner, one machine, `KM_THREADS=1`, a time limit that ended several runs, no repeats. Phase times are indicative only.
- The Protégé 6 build (OWL API 5) is not run; the module builds against OWL API 4.5.29 and HermiT 1.4.3.456.
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("outdir")
    ap.add_argument("report")
    ap.add_argument("--census")
    ap.add_argument("--adjudication")
    ap.add_argument("--diff-tsv")
    ap.add_argument("--intro", help="markdown inserted after the headline block (run settings, ontology selection)")
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
                diffs[(m, diff_kind(c))].append((name, c))
            elif v in ("km_unsupported", "km_timeout"):
                exc = c["km"].get("exc") or c["km"].get("status")
                unsup[(m, exc)].append((name, c))
        for who in ("hermit", "km"):
            rs = r["reasoners"].get(who, {})
            for ph, ms in rs.get("phase_ms", {}).items():
                phase_ms[who][ph].append((name, ms))
    methods.sort()
    onts = [n for n, _ in runs]
    # The same cells split by the kind of argument (named, anonymous expression, top/bottom, inverse).
    cells2 = defaultdict(list)
    for (m, n), lst in cells.items():
        for c, v in lst:
            tag = arg_tag(c["id"]) if m not in ("isEntailed", "isEntailmentCheckingSupported", "precomputeInferences",
                                                 "isPrecomputed") and "(" in c["id"] else ""
            cells2[(m + (" [" + tag.strip(" ()").replace(" argument", "") + "]" if tag else ""), n)].append((c, v))
    methods2 = sorted({m for m, _ in cells2})

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

    def table_counts2(mode):
        per_method = {m: Counter() for m in methods2}
        for (m, n), lst in cells2.items():
            vs = [("differ_topbottom" if (v in DIFF and topbottom_only(c)) else v) for c, v in lst]
            per_method[m][cell_kind(vs, mode)] += 1
        return per_method

    p2, p2a = table_counts2("strict"), table_counts2("adjusted")
    t2c, t2a = Counter(), Counter()
    for m in methods2:
        t2c.update(p2[m])
        t2a.update(p2a[m])
    g2, tt2 = score(t2c)
    g2a, _ = score(t2a)

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
    L.append(f"Splitting each method by the kind of argument (named entity, anonymous class expression, top or bottom entity, inverse property expression) "
             f"gives {tt2} cells and a strict score of **{100.0 * g2 / tt2:.1f}%** ({g2} cells), adjusted {100.0 * g2a / tt2:.1f}% ({g2a} cells).\n")
    L.append("A cell is one OWLReasoner method on one ontology; it counts for KM when KM agrees with HermiT on every "
             "call of that method (HermiT errors that KM answers are not held against KM), or when HermiT fails on "
             "the whole cell and KM answers. Settings: HermiT 1.4.3.456 with `ignoreUnsupportedDatatypes = true`, "
             "KM plugin through the OWL API 4.5.29, `KM_THREADS=1`.\n")
    if a.intro and os.path.exists(a.intro):
        L.append(open(a.intro).read().rstrip() + "\n")
    L.append("Call verdicts, all calls: " + ", ".join(f"{k} {v}" for k, v in sorted(verdict_total.items())) + ".\n")

    L.append("## Per method\n")
    L.append("Counts are ontologies. `strict` columns count node grouping differences as differences.\n")
    L.append("| Method | Agreed | Differed | of which only grouping | of which only top/bottom | KM unsupported | KM timeout | HermiT failed (KM answers) | Both failed | HermiT timeout (excluded) | Score |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for m in methods:
        c, cl, ca = pm[m], pm_l[m], pm_a[m]
        gd, tot = score(c)
        sc = f"{100.0 * gd / tot:.0f}%" if tot else "-"
        L.append(f"| `{m}` | {c['agree']} | {c['differ']} | {c['differ'] - cl['differ']} | {cl['differ'] - ca['differ']} "
                 f"| {c['km_unsupported']} | {c['km_timeout']} | {c['hermit_failed_km_ok']} | {c['hermit_failed_km_fail']} "
                 f"| {c['hermit_timeout']} | {sc} |")
    L.append("")

    L.append("## Per method and argument kind\n")
    L.append("Cells split by what the call was asked about, so that the answers for named entities are not hidden by the "
             "anonymous expression or top and bottom queries of the same method. Only methods whose arguments vary are split.\n")
    L.append("| Method [argument kind] | Agreed | Differed | of which only top/bottom | KM unsupported | KM timeout | HermiT failed (KM answers) | Both failed | HermiT timeout (excluded) | Score | Adjusted score |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for m in methods2:
        c, ca = p2[m], p2a[m]
        gd, tot = score(c)
        gda, _ = score(ca)
        if "[" not in m and not any(x.startswith(m + " [") for x in methods2):
            continue
        sc = f"{100.0 * gd / tot:.0f}%" if tot else "-"
        sca = f"{100.0 * gda / tot:.0f}%" if tot else "-"
        L.append(f"| `{m}` | {c['agree']} | {c['differ']} | {c['differ'] - ca['differ']} | {c['km_unsupported']} | {c['km_timeout']} "
                 f"| {c['hermit_failed_km_ok']} | {c['hermit_failed_km_fail']} | {c['hermit_timeout']} | {sc} | {sca} |")
    L.append("")

    # Call-level table: the cell view hides how many single calls agree.
    call_by_method = defaultdict(Counter)
    for (m, n), lst in cells.items():
        for c, v in lst:
            call_by_method[m][v] += 1
    L.append("## Per method, counted by call\n")
    L.append("The same data as above, one count per reasoner call instead of per method and ontology. "
             "`agree` includes both threw the same exception; `differ` includes node grouping only.\n")
    L.append("| Method | Calls | Agree | Differ | KM unsupported | KM timeout or not reached | HermiT error, KM answers | Both threw different errors | HermiT timeout (excluded) |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    for m in methods:
        c = call_by_method[m]
        tot = sum(c.values())
        L.append(f"| `{m}` | {tot} | {c['agree'] + c['both_error_same']} | {c['differ_content'] + c['differ_structure']} "
                 f"| {c['km_unsupported']} | {c['km_timeout']} | {c['hermit_error']} | "
                 f"{c['both_error_different'] + c['both_failed']} | {c['hermit_timeout']} |")
    L.append("")

    # isEntailed by axiom type.
    ent = defaultdict(Counter)
    for (m, n), lst in cells.items():
        if m != "isEntailed":
            continue
        for c, v in lst:
            inner = c["id"][len("isEntailed("):]
            typ = "set of axioms" if inner.startswith("set:") else inner.split("(", 1)[0]
            ent[typ][v] += 1
    L.append("## `isEntailed` by axiom type\n")
    L.append("One generated or ontology-taken axiom per type and ontology, as described in the plan. "
             "`KM unsupported` is `UnsupportedEntailmentTypeException`.\n")
    L.append("| Axiom type | Calls | Agree | Differ | KM unsupported | KM timeout or not reached | HermiT error | HermiT timeout (excluded) |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|")
    for typ in sorted(ent):
        c = ent[typ]
        L.append(f"| {typ} | {sum(c.values())} | {c['agree'] + c['both_error_same']} | {c['differ_content'] + c['differ_structure']} "
                 f"| {c['km_unsupported']} | {c['km_timeout']} | {c['hermit_error'] + c['both_error_different'] + c['both_failed']} | {c['hermit_timeout']} |")
    L.append("")

    # HermiT errors.
    herr = defaultdict(list)
    for name, r in runs:
        for c in r["calls"]:
            h = c.get("hermit", {})
            if h.get("status") == "exception":
                herr[(c["method"], h.get("exc"), re.sub(r"\d+", "N", (h.get("msg") or "")[:110]))].append((name, c))
    L.append("## HermiT errors\n")
    L.append("Calls where HermiT threw. KM column: how KM fared on the same calls.\n")
    L.append("| Method | HermiT exception and message | Calls | Ontologies | KM on these calls |")
    L.append("|---|---|---:|---:|---|")
    for (m, exc, msg), lst in sorted(herr.items(), key=lambda kv: -len(kv[1])):
        kc = Counter((c["km"].get("exc") or c["km"].get("status")) for _, c in lst)
        L.append(f"| `{m}` | {exc}: {msg.replace('|', '/')} | {len(lst)} | {len({o for o, _ in lst})} | "
                 + ", ".join(f"{k} {v}" for k, v in kc.most_common(3)) + " |")
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

    # Ontologies where KM refuses the whole input (classification fails), with the reason.
    refuse = defaultdict(list)
    for name, r in runs:
        for c in r["calls"]:
            if c["phase"] not in ("consistency", "precompute", "classes"):
                continue
            h, k = c.get("hermit", {}), c.get("km", {})
            if h.get("status") == "ok" and k.get("status") == "exception" and \
                    k.get("exc") not in ("ClassExpressionNotInProfileException",):
                msg = (k.get("msg") or "").replace("\n", " ")
                key = re.sub(r"\d+", "N", msg)[:150]
                refuse[key].append((name, k.get("exc"), msg[:300]))
                break
    L.append("## Ontologies KM refuses\n")
    L.append("Ontologies where KM threw while classifying (first failing call, in the consistency, precompute or class phase) and HermiT answered. "
             "The plugin retries the native run on every later call, so a refused ontology also costs about the "
             "classification time per query; several of these runs ended on the time limit for that reason.\n")
    if refuse:
        L.append("| Reason (digits shown as N) | Exception | Ontologies |")
        L.append("|---|---|---|")
        for key, lst in sorted(refuse.items(), key=lambda kv: -len(kv[1])):
            L.append(f"| {lst[0][2][:260].replace('|', '/')} | {lst[0][1]} | {', '.join(sorted({o for o, _, _ in lst}))} |")
    else:
        L.append("None.\n")
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
    L.append("Differences where both reasoners answered, grouped by method and shape. The count is calls, then ontologies. "
             "Each row gives two examples (ontology, call, difference); the raw JSON in the output directory holds all of them. "
             "Adjudication by the OWL 2 direct semantics follows in the next sections.\n")
    L.append("| Method | Shape | Calls | Ontologies | Examples |")
    L.append("|---|---|---:|---:|---|")
    for (m, kind), lst in sorted(diffs.items(), key=lambda kv: -len(kv[1])):
        ont_n = len({o for o, _ in lst})
        ex, seen_o = [], set()
        for o, c in lst:
            if o in seen_o and len(seen_o) < ont_n:
                continue
            seen_o.add(o)
            ex.append(f"{o}: `{shorten_ids(c['id'])[:110]}`: {describe(c)[:230]}".replace("|", "/"))
            if len(ex) >= 2:
                break
        L.append(f"| `{m}` | {kind} | {len(lst)} | {ont_n} | " + "<br>".join(ex) + " |")
    L.append("")
    if a.diff_tsv:
        with open(a.diff_tsv, "w") as f:
            f.write("ontology\tmethod\tkind\tcall\n")
            for (m, kind), lst in sorted(diffs.items()):
                for o, c in lst:
                    f.write(f"{o}\t{m}\t{kind}\t{c['id']}\n")

    if a.adjudication and os.path.exists(a.adjudication):
        L.append(open(a.adjudication).read())
    else:
        L.append("## Adjudication\n\nNot yet written.\n")

    L.append(NOT_COVERED)
    open(a.report, "w").write("\n".join(L) + "\n")
    print(f"score strict {100.0 * g / t:.1f}% lenient {100.0 * gl / t:.1f}% cells {t}")


if __name__ == "__main__":
    main()
