#!/usr/bin/env python3
"""Writes the hand-written rule-route certificate fixtures of
lean/run-rules-certification-gate.sh. Concepts: 0 = O (the guard), 1 = {a},
2 = A, 3 = B, 4 = C. Role 0 = r. Rule: A(x) & O(x) -> B(x); ABox: A(a)."""
import json, sys
def lit(c, neg=False): return {"concept": c, "neg": neg}
def con(c, v, neg=False): return {"concept": {"literal": lit(c, neg), "node": v}}
def cl(body, head): return {"body": body, "head": head}
base = [
    cl([con(1, 0)], [con(2, 0)]),              # 0: {a}(x) -> A(x)
    cl([con(1, 0)], [con(0, 0)]),              # 1: {a}(x) -> O(x)
    cl([con(2, 0), con(0, 0)], [con(3, 0)]),   # 2: rule A(x) & O(x) -> B(x)
]
def doc(ontology, **kw):
    d = dict(version=1, oguard=0, nominals=[1], ontology=ontology, queries=[],
             consistent=True, unsatisfiable=[], subsumptions=[], premise_subsumptions=[],
             premise_unsatisfiable=[], refutations=[], models=[])
    d.update(kw); return d
def horn(c, a): return {"horn": {"clause": c, "assignment": a}}
derive = [horn(0, [1]), horn(1, [1]), horn(2, [1])]
out = {}
# 1. Inconsistency: B(x) -> bottom; the rule fires at a.
incons = base + [cl([con(3, 0)], [])]
out["rules-route-inconsistent-valid.json"] = doc(incons, consistent=False, refutations=[
    {"claim": "inconsistent", "proof": {"bottom": {"steps": derive, "clause": 3, "assignment": [1]}}}])
# 2. Forged: the bottom clause fires at node 0, where B does not hold.
out["rules-route-inconsistent-forged.json"] = doc(incons, consistent=False, refutations=[
    {"claim": "inconsistent", "proof": {"bottom": {"steps": derive, "clause": 3, "assignment": [0]}}}])
# 3. Forged: the rule fires at the unnamed root (no O guard there).
out["rules-route-unguarded-forged.json"] = doc(incons, consistent=False, refutations=[
    {"claim": "inconsistent", "proof": {"bottom": {"steps": [horn(2, [0])], "clause": 3, "assignment": [0]}}}])
# 4. Taxonomy with a disjunction and a nominal: {a} ⊑ A, A ⊑ B (by the rule only
# at a), C ⊑ B ∨ ¬C ... queries A, B, C. Model: node 0 = a (A, B, O, {a}), node 1 = A only.
tax = base + [cl([con(4, 0)], [con(3, 0), con(2, 0)])]  # 3: C(x) -> B(x) or A(x)
model = {"node_count": 4, "labels": [[1, 2, 0, 3], [2], [4, 3], [4, 2]],
         "succ": [[], [], [], []], "pred": [[], [], [], []],
         "witnesses": [[2, 1], [3, 0], [3, 2], [4, 2], [4, 3]]}
out["rules-route-taxonomy-valid.json"] = doc(tax, queries=[2, 3, 4], models=[model])
# 5. Forged taxonomy: claims A ⊑ B. A only holds at named a under the rule; the
# unnamed element 1 is a counterexample, and no proof is given.
out["rules-route-taxonomy-forged.json"] = doc(tax, queries=[2, 3, 4], subsumptions=[[2, 3]], models=[model])
# 6. Forged model: element 0 carries {a} and A but not B, so the rule is violated.
bad = dict(model, labels=[[1, 2, 0], [2], [4, 3], [4, 2]])
out["rules-route-model-forged.json"] = doc(tax, queries=[2, 3, 4], models=[bad])
# 7. Subsumption with a split: {a} ⊑ C. C ⊑ B ∨ A, and (A or B) at a gives B
# through the rule. Query {a} ⊑ B: root 0 = {{a}, ¬B}, merged with the nominal root 1.
sub = base + [cl([con(1, 0)], [con(4, 0)]), cl([con(4, 0)], [con(3, 0), con(2, 0)])]
proof = {"split": {"steps": [{"nominal": {"concept": 1, "left": 0, "right": 1}}, horn(3, [0])],
         "clause": 4, "assignment": [0], "children": [
             {"clash": {"steps": [], "node": 0, "concept": 3}},
             {"clash": {"steps": [horn(1, [0]), horn(2, [0])], "node": 0, "concept": 3}}]}}
out["rules-route-subsumption-valid.json"] = doc(sub, queries=[1, 3], subsumptions=[[1, 3]],
    refutations=[{"claim": {"sub": {"sub": 1, "sup": 3}}, "proof": proof}],
    models=[{"node_count": 2, "labels": [[1, 2, 0, 3, 4], [3]], "succ": [[], []], "pred": [[], []],
             "witnesses": [[1, 0], [3, 1]]}])
# Root label is [{a}, ¬B]; node 0 merges into nominal root 1? keep = min = 0.
def with_ext(m):
    ext = {}
    for d, labs in enumerate(m["labels"]):
        for c in labs: ext.setdefault(c, []).append(d)
    m["ext"] = [ext.get(c, []) for c in range(1 + max(ext, default=0))]
    return m
for d in out.values():
    d["models"] = [with_ext(dict(m)) for m in d["models"]]
for name, d in out.items():
    json.dump(d, open(name, "w"), indent=1)
