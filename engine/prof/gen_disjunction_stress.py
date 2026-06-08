#!/usr/bin/env python3
"""Live-disjunction tableau stress WITH a clash trap so the tableau explores
branches and backtracks -> g.clone() fires at many choice points on a non-trivial
graph. A ⊑ ∃r.A chains (blocking bounds depth); each A-node carries K live
disjunctions C_i ⊔ D_i; C0⊓C1 and D0⊓D1 are unsat, killing two corners of the
choice cube and forcing backtracking. A stays satisfiable overall."""
import sys
K = int(sys.argv[1]) if len(sys.argv) > 1 else 6
P = int(sys.argv[2]) if len(sys.argv) > 2 else 1   # parallel role fan-out
out = ["Prefix(:=<http://ex#>)", "Ontology(", "Declaration(Class(:A))"]
for i in range(K):
    out += ["Declaration(Class(:C%d))" % i, "Declaration(Class(:D%d))" % i]
roles = ["r"] + ["r%d" % j for j in range(P)]
for r in roles:
    out.append("Declaration(ObjectProperty(:%s))" % r)
for r in roles:
    out.append("SubClassOf(:A ObjectSomeValuesFrom(:%s :A))" % r)
    for i in range(K):
        out.append("SubClassOf(:A ObjectAllValuesFrom(:%s ObjectUnionOf(:C%d :D%d)))" % (r, i, i))
out += ["SubClassOf(ObjectIntersectionOf(:C0 :C1) owl:Nothing)",
        "SubClassOf(ObjectIntersectionOf(:D0 :D1) owl:Nothing)", ")"]
print("\n".join(out))
