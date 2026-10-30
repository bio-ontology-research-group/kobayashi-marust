# Exact expected classification of the generated family ontologies for an
# empty (E) or universal (U) data range R, by enumerating element types.
import itertools, json, sys
def classify(kind):
    types = []
    for n, v1, ne, ev1, a, b in itertools.product([0,1,2],[0,1],[0,1],[0,1],[0,1],[0,1]):
        if v1 and n == 0: continue
        if ev1 and ne == 0: continue
        if kind == "E" and ne: continue          # DataPropertyRange(e R), R empty
        if a and n == 0: continue
        if b and n != 0: continue
        k = 0 if kind == "E" else n             # number of d-values in R
        allR = (k == n)
        c = dict(Has=n>=1, Two=n>=2, No=n==0, AtMostOne=n<=1,
                 Some=k>=1, All=allR, Min1=k>=1, Min2=k>=2, Max0=k==0, Max1=k<=1,
                 Exact0=k==0, Exact1=k==1, SomeLitAllR=n>=1 and allR,
                 HasValAllR=bool(v1) and allR and (kind=="U"),
                 NotSome=not k>=1, NotAll=not allR, HasE=ne>=1, HasEval=bool(ev1),
                 A=bool(a), B=bool(b))
        # HasValAllR for E: value 1 must be in R -> impossible
        types.append(c)
    names = sorted(types[0])
    unsat = sorted(x for x in names if not any(t[x] for t in types))
    subs = sorted([x, y] for x in names for y in names if x != y and x not in unsat
                  and y not in unsat and all(t[y] for t in types if t[x]))
    return {"subsumptions": subs, "unsatisfiable": unsat}
print(json.dumps(classify(sys.argv[1])))
