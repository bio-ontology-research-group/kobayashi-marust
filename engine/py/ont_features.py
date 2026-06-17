#!/usr/bin/env python3
"""Structural feature extraction for the KM routing decision tree.

Runs the `ofn` frontend on an ontology and computes a vector of *structural*
DL-clause features (never the ontology identity — see the no-benchmark-hardcoding
rule). These features feed `route_tree.py`, which learns a decision tree that
maps features -> which KM engine/config to route the ontology to.

The clause set is read in split mode (`ofn <ont> --meta <metafile>`, clauses to
stdout) and **streamed** with ijson when available, so the 3 ORE giants
(450-580 MB, multi-million clauses) never materialise in Python memory. Falls
back to json.load for small ontologies / when ijson is absent.

Usage:
    python3 ont_features.py <ont.owl>                 # print one feature JSON
    python3 ont_features.py --batch list.txt --out features.jsonl [--corpus DIR]
    # env: KM_OFN_BIN overrides the ofn binary path
"""
import json, os, subprocess, sys, tempfile, argparse

HERE = os.path.dirname(os.path.abspath(__file__))

def ofn_bin():
    return os.environ.get("KM_OFN_BIN", os.path.join(HERE, "..", "target", "release", "ofn"))

try:
    import ijson  # streaming JSON; optional
    HAVE_IJSON = True
except Exception:
    HAVE_IJSON = False


# ---------------------------------------------------------------------------
# Feature accumulator: one streaming pass over the clause set.
# ---------------------------------------------------------------------------
class Acc:
    def __init__(self):
        self.n_clauses = 0
        self.concepts = set()
        self.roles = set()
        self.n_disj = 0            # head with >=2 concept atoms (a real disjunction)
        self.max_disj_w = 0
        self.n_top = 0             # empty body (tautological/global head)
        self.n_top_disj2 = 0       # empty body + exactly 2 head concepts (excluded-middle half)
        self.n_bottom = 0          # empty head (body -> bottom / clash clause)
        self.n_bottom2 = 0         # empty head + exactly 2 body concepts (complementary half)
        self.n_exist = 0           # clause introducing a functional (Skolem) term -> existential
        self.n_eq = 0              # clause with an eq atom (number/nominal/functional signal)
        self.n_aux = 0             # clause mentioning an aux (context) term
        self.n_horn = 0            # head has <=1 concept atom
        self.has_trans = False
        self.n_chain = 0           # role-chain clause r(x,y),s(y,z) -> t(x,z)
        self.sum_body = 0
        self.max_body = 0
        self.sum_head = 0
        self.max_head = 0
        # complementary-definer detection (the EMELIM / disjunction-family signal):
        # collect concept-pairs from 2-concept top disjunctions and 2-concept
        # bottom clauses; their intersection = forced excluded-middle definers.
        self._top_pairs = set()
        self._bot_pairs = set()

    @staticmethod
    def _is_fun(term):
        return isinstance(term, dict) and term.get("kind") == "fun"

    @staticmethod
    def _is_aux(term):
        return isinstance(term, dict) and term.get("kind") == "aux"

    def add(self, c):
        body = c.get("body", []) or []
        head = c.get("head", []) or []
        self.n_clauses += 1
        bc = []   # body concept names
        hc = []   # head concept names
        broles = []
        hroles = []
        saw_fun = False
        saw_aux = False
        saw_eq = False
        for a in body:
            k = a.get("kind")
            if k == "concept":
                self.concepts.add(a.get("concept")); bc.append(a.get("concept"))
                t = a.get("term")
                if self._is_fun(t): saw_fun = True
                if self._is_aux(t): saw_aux = True
            elif k == "role":
                self.roles.add(a.get("role")); broles.append(a.get("role"))
                for t in (a.get("source"), a.get("target")):
                    if self._is_fun(t): saw_fun = True
                    if self._is_aux(t): saw_aux = True
            elif k == "eq":
                saw_eq = True
        for a in head:
            k = a.get("kind")
            if k == "concept":
                self.concepts.add(a.get("concept")); hc.append(a.get("concept"))
                t = a.get("term")
                if self._is_fun(t): saw_fun = True
                if self._is_aux(t): saw_aux = True
            elif k == "role":
                self.roles.add(a.get("role")); hroles.append(a.get("role"))
                for t in (a.get("source"), a.get("target")):
                    if self._is_fun(t): saw_fun = True
                    if self._is_aux(t): saw_aux = True
            elif k == "eq":
                saw_eq = True

        nb = len(body); nh = len(head)
        self.sum_body += nb; self.max_body = max(self.max_body, nb)
        self.sum_head += nh; self.max_head = max(self.max_head, nh)
        if saw_fun: self.n_exist += 1
        if saw_aux: self.n_aux += 1
        if saw_eq: self.n_eq += 1

        if len(hc) >= 2:
            self.n_disj += 1
            self.max_disj_w = max(self.max_disj_w, len(hc))
        if len(hc) <= 1:
            self.n_horn += 1
        if nb == 0:
            self.n_top += 1
            if len(hc) == 2:
                self.n_top_disj2 += 1
                self._top_pairs.add(frozenset(hc))
        if nh == 0:
            self.n_bottom += 1
            if len(bc) == 2:
                self.n_bottom2 += 1
                self._bot_pairs.add(frozenset(bc))

        # transitivity / role chains:  r(x,y) & s(y,z) -> t(x,z), no head concept
        if len(broles) == 2 and len(hroles) == 1 and not hc:
            self.n_chain += 1
            r = hroles[0]
            if broles[0] == r and broles[1] == r:
                self.has_trans = True

    def finalize(self, meta):
        n = max(self.n_clauses, 1)
        named = set(meta.get("named", []) or [])
        feats = {
            "n_clauses": self.n_clauses,
            "n_concept": len(self.concepts),
            "n_role": len(self.roles),
            "n_named": len(named),
            "n_declared": len(meta.get("declared", []) or []),
            "n_disj": self.n_disj,
            "max_disj_width": self.max_disj_w,
            "frac_disj": round(self.n_disj / n, 5),
            "n_top": self.n_top,
            "n_top_disj2": self.n_top_disj2,
            "n_bottom": self.n_bottom,
            "n_bottom2": self.n_bottom2,
            # complementary excluded-middle definers (5303 disjunction-family / EMELIM signal)
            "n_compl_definer": len(self._top_pairs & self._bot_pairs),
            "n_exist": self.n_exist,
            "frac_exist": round(self.n_exist / n, 5),
            "n_eq": self.n_eq,
            "n_aux": self.n_aux,
            "n_horn": self.n_horn,
            "frac_horn": round(self.n_horn / n, 5),
            "is_pure_horn": int(self.n_disj == 0),
            "has_trans": int(self.has_trans),
            "n_chain": self.n_chain,
            "avg_body_len": round(self.sum_body / n, 4),
            "max_body_len": self.max_body,
            "avg_head_len": round(self.sum_head / n, 4),
            "max_head_len": self.max_head,
            "el_rbox_safe": int(bool(meta.get("el_rbox_safe", False))),
        }
        return feats


# ---------------------------------------------------------------------------
# Driver: run ofn in split mode, stream the clause file.
# ---------------------------------------------------------------------------
def extract(ont_path, ofn=None):
    ofn = ofn or ofn_bin()
    res = {"ont": os.path.basename(ont_path)}
    if not os.path.exists(ont_path):
        res["status"] = "no_owl"; return res
    with tempfile.TemporaryDirectory() as td:
        clauses_path = os.path.join(td, "clauses.json")
        meta_path = os.path.join(td, "meta.json")
        try:
            with open(clauses_path, "w") as cf:
                p = subprocess.run([ofn, ont_path, "--meta", meta_path],
                                   stdout=cf, stderr=subprocess.PIPE, text=True, timeout=600)
        except subprocess.TimeoutExpired:
            res["status"] = "ofn_timeout"; return res
        if p.returncode == 3:
            res["status"] = "ofn_unsupported"; return res
        if p.returncode != 0:
            res["status"] = "ofn_fail"; res["err"] = (p.stderr or "")[-160:]; return res
        try:
            with open(meta_path) as mf:
                meta = json.load(mf)
        except Exception:
            meta = {}
        acc = Acc()
        try:
            sz = os.path.getsize(clauses_path)
            if HAVE_IJSON and sz > 50_000_000:           # stream the giants
                with open(clauses_path, "rb") as f:
                    for c in ijson.items(f, "clauses.item"):
                        acc.add(c)
            else:
                with open(clauses_path) as f:
                    for c in json.load(f).get("clauses", []):
                        acc.add(c)
        except Exception as e:
            res["status"] = "parse_fail"; res["err"] = str(e)[:160]; return res
    res.update(acc.finalize(meta))
    res["status"] = "ok"
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ont", nargs="?", help="single ontology .owl path")
    ap.add_argument("--batch", help="file with one ontology path (or ore_ont_NNN) per line")
    ap.add_argument("--corpus", help="dir to resolve bare ids/names from in --batch mode")
    ap.add_argument("--out", help="write JSONL here in --batch mode (default stdout)")
    ap.add_argument("--ofn", help="ofn binary (default $KM_OFN_BIN or repo target)")
    args = ap.parse_args()
    ofn = args.ofn or ofn_bin()

    if args.batch:
        out = open(args.out, "w", buffering=1) if args.out else sys.stdout
        for ln in open(args.batch):
            name = ln.strip()
            if not name:
                continue
            path = name
            if args.corpus and not os.path.isabs(name):
                cand = os.path.join(args.corpus, name)
                if not os.path.exists(cand) and not name.endswith(".owl"):
                    cand = os.path.join(args.corpus, name + ".owl")
                path = cand
            rec = extract(path, ofn)
            out.write(json.dumps(rec) + "\n"); out.flush()
            sys.stderr.write("feat %s -> %s\n" % (rec.get("ont"), rec.get("status")))
        if args.out:
            out.close()
        return
    if not args.ont:
        ap.error("give an ontology path or --batch")
    print(json.dumps(extract(args.ont, ofn), indent=2))


if __name__ == "__main__":
    main()
