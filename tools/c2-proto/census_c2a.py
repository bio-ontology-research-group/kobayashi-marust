"""Census of nominal patterns in the pool (design section 7).

For every admitted pool input with nominals (census column O = 1):

* syntactic scan of the OWL file: ObjectOneOf arities (one individual or
  several), ObjectHasValue, SameIndividual, DifferentIndividuals;
* the C2a test on km's normalised DL clauses (`km ofn`): is there a lower
  clause (existential or at-least, written as a head role atom to a
  function term or an individual) whose subject is not a nominal proxy,
  with role S, and an at-most clause (an equality head) with counted role
  R such that S is below the inverse of R in the role hierarchy of the
  clauses? If not, the input is in C2a.

    python census_c2a.py OUT.tsv [max_inputs]

Runs at most two km processes at once, 600 s each.
"""

from __future__ import annotations

import csv
import json
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

CENSUS = "/mnt/data1/leechuck/km-work/v170/reports/census-per-input.tsv"
CORPUS = "/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files"
KM = os.environ.get("C2_KM", "/mnt/data1/leechuck/km-work/v170/scratch/w2p/km")
SCRATCH = os.environ.get("C2_SCRATCH", "/mnt/data1/leechuck/km-work/v170/scratch/c2")
TMP = os.path.join(SCRATCH, "tmp")

ONEOF = re.compile(r"ObjectOneOf\(([^()]*)\)")
TOKEN = re.compile(r"<[^>]*>|[^\s()]+")


def scan_owl(path):
    one = several = hv = same = diff = 0
    carry = ""
    with open(path, "r", errors="replace") as f:
        while True:
            block = f.read(1 << 24)
            if not block:
                break
            text = carry + block
            cut = text.rfind("\n")
            if cut < 0:
                carry = text
                continue
            text, carry = text[:cut], text[cut:]
            for m in ONEOF.finditer(text):
                k = len(TOKEN.findall(m.group(1)))
                if k == 1:
                    one += 1
                else:
                    several += 1
            hv += text.count("ObjectHasValue(")
            same += text.count("SameIndividual(")
            diff += text.count("DifferentIndividuals(")
    return {"oneof1": one, "oneofN": several, "hasvalue": hv, "same": same, "diff": diff}


def term_var(t):
    return t["name"] if t["kind"] == "var" else None


def analyse_clauses(path):
    with open(path) as f:
        d = json.load(f)
    clauses = d["clauses"]
    sub = []  # (R, S) role terms (name, inv)
    lower = []
    upper = []
    for c in clauses:
        body, head = c["body"], c["head"]
        # role inclusions R(x,y) -> S(x,y) / S(y,x)
        if len(body) == 1 and body[0]["kind"] == "role" and head and all(a["kind"] == "role" for a in head) \
                and len(head) == 1:
            b, h = body[0], head[0]
            bx, by = term_var(b["source"]), term_var(b["target"])
            hx, hy = term_var(h["source"]), term_var(h["target"])
            if bx and by and hx and hy:
                same_dir = (hx, hy) == (bx, by)
                sub.append(((b["role"], False), (h["role"], not same_dir)))
                continue
        # lower: a head role atom between x and a function term or an individual
        for a in head:
            if a["kind"] != "role":
                continue
            s, t = a["source"], a["target"]
            if s["kind"] == "var" and t["kind"] in ("fun", "ind"):
                x, S = s["name"], (a["role"], False)
            elif t["kind"] == "var" and s["kind"] in ("fun", "ind"):
                x, S = t["name"], (a["role"], True)
            else:
                continue
            nominal_subject = any(b["kind"] == "concept" and b["concept"].startswith("__nom__")
                                  and term_var(b["term"]) == x for b in body)
            if body and not nominal_subject:
                lower.append(S)
            elif not body:
                pass  # ground fact about an individual: a core-core edge
        # upper: an equality in the head between successor variables
        if any(a["kind"] == "eq" for a in head):
            eqvars = set()
            for a in head:
                if a["kind"] == "eq":
                    for t in (a["left"], a["right"]):
                        if t["kind"] == "var":
                            eqvars.add(t["name"])
            for b in body:
                if b["kind"] != "role":
                    continue
                s, t = term_var(b["source"]), term_var(b["target"])
                if s and t:
                    if t in eqvars and s not in eqvars:
                        upper.append((b["role"], False))
                    elif s in eqvars and t not in eqvars:
                        upper.append((b["role"], True))
    for card in d.get("cardinalities", []):
        R = (card["role"], False)
        if card.get("min"):
            lower.append(R)
        else:
            upper.append(R)
    # role hierarchy closure over role terms
    edges = set()
    for (R, S) in sub:
        edges.add((R, S))
        edges.add(((R[0], not R[1]), (S[0], not S[1])))
    succ = {}
    for (a, b) in edges:
        succ.setdefault(a, set()).add(b)

    def up(S):
        seen = {S}
        stack = [S]
        while stack:
            x = stack.pop()
            for y in succ.get(x, ()):
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    upper_flipped = {(R[0], not R[1]) for R in upper}
    witness = None
    for S in set(lower):
        hit = up(S) & upper_flipped
        if hit:
            witness = (S, sorted(hit)[0])
            break
    return {"n_clauses": len(clauses), "n_lower": len(lower), "n_upper": len(upper),
            "c2a": witness is None, "c2a_witness": json.dumps(witness) if witness else ""}


def one(row):
    name = row["ontology"]
    owl = os.path.join(CORPUS, name + ".owl")
    res = {"ontology": name, "bytes": row["bytes"], "I": row["I"], "Q": row["Q"],
           "fragment": row["fragment"]}
    res.update(scan_owl(owl))
    out = os.path.join(SCRATCH, "census-ofn", name + ".json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    env = dict(os.environ, TMPDIR=TMP, KM_THREADS="1")
    try:
        with open(out, "w") as f:
            r = subprocess.run(["timeout", "600", KM, "ofn", owl], stdout=f,
                               stderr=subprocess.PIPE, text=True, env=env, timeout=620)
        if r.returncode != 0:
            res["km_ofn"] = f"rc {r.returncode}: " + (r.stderr.strip().splitlines() or [""])[-1][:120]
        else:
            res["km_ofn"] = "ok"
            res.update(analyse_clauses(out))
    except Exception as e:  # noqa: BLE001
        res["km_ofn"] = f"error: {e}"[:150]
    finally:
        if os.path.exists(out):
            os.remove(out)
    return res


def main():
    out = sys.argv[1]
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else None
    rows = [r for r in csv.DictReader(open(CENSUS), delimiter="\t")
            if r["admission"] == "checks_passed" and r["O"] == "1"]
    rows.sort(key=lambda r: int(r["bytes"]))
    if limit:
        rows = rows[:limit]
    cols = ["ontology", "bytes", "fragment", "I", "Q", "oneof1", "oneofN", "hasvalue", "same", "diff",
            "km_ofn", "n_clauses", "n_lower", "n_upper", "c2a", "c2a_witness"]
    with open(out, "w") as f, ThreadPoolExecutor(max_workers=2) as ex:
        f.write("\t".join(cols) + "\n")
        for res in ex.map(one, rows):
            f.write("\t".join(str(res.get(c, "")) for c in cols) + "\n")
            f.flush()
            print(res["ontology"], res.get("km_ofn"), res.get("c2a"), flush=True)


if __name__ == "__main__":
    main()
