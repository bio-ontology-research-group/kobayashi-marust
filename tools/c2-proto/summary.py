"""Summary tables of validate.py results (design section 9).

    python summary.py results-hand.jsonl [results-random-1.jsonl ...]
"""

import json
import sys
from collections import Counter


def hand_table(paths):
    """Markdown table of the hand cases; the first file that decided a case
    wins (pass the runs with the largest core limit first)."""
    from cases import CASES
    runs = [{json.loads(l)["name"]: json.loads(l) for l in open(p)} for p in paths]
    print("| Case | Expected | HermiT | Procedure (core limit) | Core | Finite model | NI steps |")
    print("|---|---|---|---|---:|---:|---:|")
    for (name, _, exp, _) in CASES:
        r = next((run[name] for run in runs if name in run and run[name]["proc"] is not None),
                 next(run[name] for run in runs if name in run))
        p = r["proc"]
        proc = "timeout" if p is None else ("realisation" if p else "none")
        st = r.get("steer_stats", {})
        print(f"| `{name}` | {'cons.' if exp else 'incons.'} | {r['hermit']} | {proc} (≤ {r['kmax']}) | "
              f"{r.get('core_size', '')} | {r['bf'] if r['bf'] is not None else '–'} | "
              f"{st.get('ni', '') if r['bf'] is not None else ''} |")


def main():
    if sys.argv[1] == "--hand":
        hand_table(sys.argv[2:])
        return
    for path in sys.argv[1:]:
        rows = [json.loads(line) for line in open(path)]
        c = Counter()
        for r in rows:
            c["queries"] += 1
            p, h, k = r["proc"], r.get("hermit"), r.get("km")
            c[f"proc {p}"] += 1
            c[f"hermit {h if h in ('true', 'false') else 'other'}"] += 1
            if k is not None:
                c[f"km {k if k in ('true', 'false') else 'other'}"] += 1
            if p is not None and h in ("true", "false"):
                c["proc=hermit" if p == (h == "true") else "proc!=hermit"] += 1
            if k in ("true", "false") and h in ("true", "false"):
                c["km=hermit" if k == h else "km!=hermit"] += 1
            if r.get("check") is not None:
                c[f"hint check {r['check']}"] += 1
            if r["bf"] is not None:
                c["finite model found"] += 1
                c[f"cert {r.get('cert')}"] += 1
                c[f"steer {r.get('steer')}"] += 1
                st = r.get("steer_stats", {})
                if st.get("ni", 0):
                    c["steer with NI"] += 1
                c[f"steer max idep {st.get('max_idep', '-')}"] += 1
                if r.get("cert_promotions", 0):
                    c["cert with promotions"] += 1
            if r.get("c2a_input"):
                c["C2a inputs"] += 1
                if r.get("c2a") is not None and p is not None:
                    c["C2a=proc" if r["c2a"] == p else "C2a!=proc"] += 1
            if p and r.get("core_size", 0) > max(1, r["text"].count("nom ")):
                c["proc core > nominal names"] += 1
            if p is None and h == "false":
                c["timeout, HermiT inconsistent"] += 1
            if p is None and h == "true":
                c["timeout, HermiT consistent"] += 1
            if r["problems"] and not all(x == "proc timeout" for x in r["problems"]):
                c["queries with a real problem"] += 1
        print(f"== {path}")
        for key in sorted(c):
            print(f"  {key}: {c[key]}")


if __name__ == "__main__":
    main()
