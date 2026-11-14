"""Independent reference: finite models up to a domain size, by SAT.

Encodes "the knowledge base has a model over {0..N-1}" directly from the
Tarskian semantics of the clauses (`SRIQ.satClause` plus `nom`), with
CaDiCaL through python-sat. Shares nothing with realise.py except the
clause syntax. A model found proves consistency; no model up to N proves
nothing (the knowledge base may need a larger or an infinite model).
"""

from __future__ import annotations

from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153

from kb import KB


class _Pool:
    def __init__(self):
        self.top = 0
        self.ids = {}

    def id(self, key):
        if key not in self.ids:
            self.top += 1
            self.ids[key] = self.top
        return self.ids[key]


def has_model(kb: KB, N: int, want_model=False):
    pool = _Pool()
    cls = []

    def C(a, x):
        return pool.id(("c", a, x))

    def Rn(r, x, y):  # named role r
        return pool.id(("r", r, x, y))

    def RT(R, x, y):  # role term
        return Rn(R // 2, x, y) if R % 2 == 0 else Rn(R // 2, y, x)

    D = range(N)

    def card(lits, k, atleast):
        enc = (CardEnc.atleast if atleast else CardEnc.atmost)(
            lits=lits, bound=k, top_id=pool.top, encoding=EncType.seqcounter)
        pool.top = max(pool.top, enc.nv)
        return enc.clauses

    for cl in kb.clauses:
        kind = cl[0]
        if kind == "gci":
            body, head = cl[1], cl[2]
            for x in D:
                cls.append([-C(a, x) for a in body] + [C(b, x) for b in head])
        elif kind == "all":
            a, R, b = cl[1:]
            for x in D:
                for y in D:
                    cls.append([-C(a, x), -RT(R, x, y), C(b, y)])
        elif kind in ("ex", "ge", "le"):
            if kind == "ex":
                a, R, b = cl[1:]
                k = 1
            else:
                a, k, R, b = cl[1:]
            for x in D:
                zs = []
                for y in D:
                    z = pool.id(("z", kind, cl, x, y))
                    # z <-> RT(R,x,y) & C(b,y)
                    cls.append([-z, RT(R, x, y)])
                    cls.append([-z, C(b, y)])
                    cls.append([z, -RT(R, x, y), -C(b, y)])
                    zs.append(z)
                g = pool.id(("g", cl, x))  # g <-> C(a,x)
                cls.append([-g, C(a, x)])
                cls.append([g, -C(a, x)])
                if kind in ("ex", "ge"):
                    if k == 0:
                        continue
                    if k > N:
                        cls.append([-g])
                        continue
                    for c in card(zs, k, True):
                        cls.append([-g] + c)
                else:
                    if k >= N:
                        continue
                    for c in card(zs, k, False):
                        cls.append([-g] + c)
        elif kind == "sub":
            R, S = cl[1:]
            for x in D:
                for y in D:
                    cls.append([-RT(R, x, y), RT(S, x, y)])
        elif kind == "nom":
            a = cl[1]
            lits = [C(a, x) for x in D]
            cls.append(lits)
            cls.extend(card(lits, 1, False))
    with Cadical153(bootstrap_with=cls) as s:
        ok = s.solve()
        if ok and want_model:
            model = set(v for v in s.get_model() if v > 0)
            cext = {a: [x for x in D if C(a, x) in model] for a in range(kb.n)}
            rext = {r: [(x, y) for x in D for y in D if Rn(r, x, y) in model] for r in range(kb.m)}
            return True, (cext, rext)
        return ok, None


def find_model(kb: KB, Nmax: int):
    """Smallest N <= Nmax with a model, or None."""
    for N in range(1, Nmax + 1):
        ok, _ = has_model(kb, N)
        if ok:
            return N
    return None
