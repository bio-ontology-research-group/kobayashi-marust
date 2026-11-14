"""Normal-form knowledge bases with nominals (stage C2 prototype).

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`, section 1. Concepts are ints
`0..n-1`, roles ints `0..m-1`. A role term (`RoleT`) is `2*r` for `r` and
`2*r+1` for `r⁻`; `flip(R) = R ^ 1`.

Clauses (tuples):

* `('gci', body, head)`   ⊓body ⊑ ⊔head (tuples of concepts)
* `('ex', a, R, b)`       a ⊑ ∃R.b
* `('all', a, R, b)`      a ⊑ ∀R.b
* `('ge', a, k, R, b)`    a ⊑ ≥k R.b
* `('le', a, k, R, b)`    a ⊑ ≤k R.b
* `('sub', R, S)`         R ⊑ S (a role chain of length one)
* `('nom', a)`            a is interpreted as exactly one element

This is the `SRIQ` normal form of `lean/ContextCalculus/SRIQ/NormalForm.lean`
with transitivity already removed, plus `nom`.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import cached_property
from itertools import combinations


def flip(R: int) -> int:
    return R ^ 1


def flipL(L: frozenset) -> frozenset:
    return frozenset(R ^ 1 for R in L)


@dataclass(frozen=True)
class KB:
    n: int
    m: int
    clauses: tuple
    cnames: tuple = ()
    rnames: tuple = ()

    # ---- naming -------------------------------------------------------
    def cname(self, a: int) -> str:
        return self.cnames[a] if a < len(self.cnames) else f"C{a}"

    def rname(self, R: int) -> str:
        base = self.rnames[R // 2] if R // 2 < len(self.rnames) else f"r{R // 2}"
        return base + ("-" if R & 1 else "")

    def show(self) -> str:
        out = []
        c, r = self.cname, self.rname
        for cl in self.clauses:
            k = cl[0]
            if k == "gci":
                out.append(" & ".join(map(c, cl[1])) or "T")
                out[-1] += " <= " + (" | ".join(map(c, cl[2])) or "F")
            elif k == "ex":
                out.append(f"{c(cl[1])} <= some {r(cl[2])}.{c(cl[3])}")
            elif k == "all":
                out.append(f"{c(cl[1])} <= all {r(cl[2])}.{c(cl[3])}")
            elif k == "ge":
                out.append(f"{c(cl[1])} <= >={cl[2]} {r(cl[3])}.{c(cl[4])}")
            elif k == "le":
                out.append(f"{c(cl[1])} <= <={cl[2]} {r(cl[3])}.{c(cl[4])}")
            elif k == "sub":
                out.append(f"{r(cl[1])} <= {r(cl[2])}")
            elif k == "nom":
                out.append(f"nom {c(cl[1])}")
        return "\n".join(out)

    # ---- derived tables ------------------------------------------------
    @cached_property
    def cache(self) -> dict:
        """Per-KB memo table (avoids hashing the KB on every lookup)."""
        return {}

    @cached_property
    def noms(self) -> frozenset:
        return frozenset(cl[1] for cl in self.clauses if cl[0] == "nom")

    @cached_property
    def gcis(self):
        return [(frozenset(cl[1]), frozenset(cl[2])) for cl in self.clauses if cl[0] == "gci"]

    @cached_property
    def alls(self):
        return [cl[1:] for cl in self.clauses if cl[0] == "all"]

    @cached_property
    def lower(self):
        """(a, k, R, b); an existential counts as k = 1 (`SRIQ.lowerL`)."""
        out = []
        for cl in self.clauses:
            if cl[0] == "ex":
                out.append((cl[1], 1, cl[2], cl[3]))
            elif cl[0] == "ge":
                out.append(cl[1:])
        return out

    @cached_property
    def upper(self):
        return [cl[1:] for cl in self.clauses if cl[0] == "le"]

    @cached_property
    def bnd(self) -> int:
        return sum(q[1] for q in self.lower)

    @cached_property
    def role_le(self) -> dict:
        """`RoleLe`: reflexive-transitive closure of the inclusions and
        their flips. Maps R to the set of S with R ⊑* S."""
        nr = 2 * self.m
        up = {R: {R} for R in range(nr)}
        edges = []
        for cl in self.clauses:
            if cl[0] == "sub":
                edges.append((cl[1], cl[2]))
                edges.append((flip(cl[1]), flip(cl[2])))
        changed = True
        while changed:
            changed = False
            for R in range(nr):
                for (a, b) in edges:
                    if a in up[R] and b not in up[R]:
                        up[R].add(b)
                        changed = True
        return {R: frozenset(v) for R, v in up.items()}

    def up_closed(self, L) -> bool:
        return all(self.role_le[R] <= L for R in L)

    def up_close(self, L) -> frozenset:
        out = set()
        for R in L:
            out |= self.role_le[R]
        return frozenset(out)

    @cached_property
    def need_roles(self) -> frozenset:
        """Roles of lower clauses and their inverses."""
        out = set()
        for (a, k, R, b) in self.lower:
            out.add(R)
            out.add(flip(R))
        return frozenset(out)

    def shrink(self, L) -> frozenset:
        """Minimal label (design lemma 3.6): up(L ∩ need_roles) ⊆ L."""
        return self.up_close(L & self.need_roles)

    @cached_property
    def labels(self) -> list:
        """The nonempty minimal labels: up-closures of nonempty sets of
        need roles. Every realisation stays a realisation when each label
        L is replaced by `shrink(L)` (design lemma 3.6), so searches range
        over these labels only."""
        nr = sorted(self.need_roles)
        out = set()
        for mask in range(1, 1 << len(nr)):
            S = frozenset(nr[i] for i in range(len(nr)) if mask >> i & 1)
            out.add(self.up_close(S))
        return sorted(out, key=lambda L: (len(L), sorted(L)))

    def closed(self, t) -> bool:
        return all(not (body <= t) or bool(head & t) for body, head in self.gcis)

    @cached_property
    def types(self) -> list:
        """All closed types."""
        out = []
        for mask in range(1 << self.n):
            t = frozenset(a for a in range(self.n) if mask >> a & 1)
            if self.closed(t):
                out.append(t)
        return out

    @cached_property
    def tree_types(self) -> list:
        """Closed types without a nominal name."""
        return [t for t in self.types if not (t & self.noms)]

    # ---- star conditions (SRIQ/Stars.lean) -----------------------------
    def edge_ok(self, t, L, s) -> bool:
        for (a, S, c) in self.alls:
            if S in L and a in t and c not in s:
                return False
            if flip(S) in L and a in s and c not in t:
                return False
        return True

    def counted(self, d_type, L_from_d, t) -> bool:
        """Some at-most clause firing at a centre of type `d_type` counts a
        neighbour of type `t` reached by label `L_from_d`."""
        return any(a in d_type and R in L_from_d and b in t for (a, k, R, b) in self.upper)

    def star_ok(self, t, N) -> bool:
        """`StarOK O t N` for a list of entries (label, type)."""
        if not self.closed(t):
            return False
        for (L, s) in N:
            if not self.up_closed(L) or not self.edge_ok(t, L, s):
                return False
        for (a, k, R, b) in self.lower:
            if a in t and sum(1 for (L, s) in N if R in L and b in s) < k:
                return False
        for (a, k, R, b) in self.upper:
            if a in t and sum(1 for (L, s) in N if R in L and b in s) > k:
                return False
        return True

    # ---- fresh names (reductions of section 5) --------------------------
    def with_clauses(self, extra, n_extra=0, names=()) -> "KB":
        return KB(self.n + n_extra, self.m, tuple(self.clauses) + tuple(extra),
                  tuple(self.cnames) + tuple(names), self.rnames)

    def sat_query(self, a: int) -> "KB":
        """Consistent iff concept `a` is satisfiable: a fresh nominal X ⊑ a."""
        X = self.n
        return self.with_clauses([("nom", X), ("gci", (X,), (a,))], 1, (f"X_{self.cname(a)}",))

    def nonsub_query(self, a: int, b: int) -> "KB":
        """Consistent iff a ⊑ b is NOT entailed."""
        X = self.n
        return self.with_clauses([("nom", X), ("gci", (X,), (a,)), ("gci", (X, b), ())], 1,
                                 (f"X_{self.cname(a)}",))

    # ---- syntactic sub-case C2a -----------------------------------------
    def is_c2a(self) -> bool:
        """No lower clause on a non-nominal subject whose role is below the
        inverse of a role of an at-most clause (design section 7)."""
        for (a, k, S, b) in self.lower:
            if a in self.noms:
                continue
            for (a2, k2, R, b2) in self.upper:
                if flip(R) in self.role_le[S]:
                    return False
        return True


def parse(text: str) -> KB:
    """A small text syntax, one clause per line:

        A & B <= C | D      (T / F for empty sides)
        A <= some r.B   A <= all r-.B   A <= >=2 r.B   A <= <=1 r-.B
        role r <= s-        (role inclusion)
        nom O               (O is a nominal name)
        distinct A B C      (pairwise disjoint)
        anon A B            (A, B hold at no nominal element)
    """
    cn: dict = {}
    rn: dict = {}

    def c(x):
        x = x.strip()
        if x not in cn:
            cn[x] = len(cn)
        return cn[x]

    def role(x):
        x = x.strip()
        inv = x.endswith("-")
        base = x[:-1] if inv else x
        if base not in rn:
            rn[base] = len(rn)
        return 2 * rn[base] + (1 if inv else 0)

    cls = []
    anon = []
    for line in text.splitlines():
        line = line.split("#")[0].strip()
        if not line:
            continue
        if line.startswith("nom "):
            cls.append(("nom", c(line[4:])))
            continue
        if line.startswith("anon "):  # these names hold at no nominal element
            anon.extend(c(x) for x in line[5:].split())
            continue
        if line.startswith("distinct "):
            xs = [c(x) for x in line[9:].split()]
            for i in range(len(xs)):
                for j in range(i + 1, len(xs)):
                    cls.append(("gci", (xs[i], xs[j]), ()))
            continue
        if line.startswith("role "):
            lhs, rhs = line[5:].split("<=")
            cls.append(("sub", role(lhs), role(rhs)))
            continue
        lhs, rhs = [s.strip() for s in line.split("<=", 1)]
        if rhs.startswith("some ") or rhs.startswith("all "):
            kind, rest = rhs.split(" ", 1)
            r, b = rest.split(".", 1)
            cls.append(("ex" if kind == "some" else "all", c(lhs), role(r), c(b)))
        elif rhs.startswith(">=") or rhs.startswith("<="):
            kind = "ge" if rhs.startswith(">=") else "le"
            num, rest = rhs[2:].split(" ", 1)
            r, b = rest.split(".", 1)
            cls.append((kind, c(lhs), int(num), role(r), c(b)))
        else:
            body = () if lhs == "T" else tuple(c(x) for x in lhs.split("&"))
            head = () if rhs == "F" else tuple(c(x) for x in rhs.split("|"))
            cls.append(("gci", body, head))
    for x in anon:
        for cl in list(cls):
            if cl[0] == "nom":
                cls.append(("gci", (x, cl[1]), ()))
    if "T" in cn:  # the name T in a filler or head is the top concept
        cls.append(("gci", (), (cn["T"],)))
    names = [None] * len(cn)
    for k, v in cn.items():
        names[v] = k
    rnames = [None] * len(rn)
    for k, v in rn.items():
        rnames[v] = k
    return KB(len(cn), max(1, len(rn)), tuple(cls), tuple(names), tuple(rnames) or ("r",))


def to_ofn(kb: KB) -> str:
    """OWL functional syntax for HermiT and km."""
    def C(a):
        return f":{kb.cname(a)}"

    def R(x):
        base = f":{kb.rnames[x // 2] if x // 2 < len(kb.rnames) else f'r{x // 2}'}"
        return f"ObjectInverseOf({base})" if x & 1 else base

    def conj(xs, empty):
        xs = [C(a) for a in xs]
        if not xs:
            return empty
        return xs[0] if len(xs) == 1 else "ObjectIntersectionOf(" + " ".join(xs) + ")"

    def disj(xs, empty):
        xs = [C(a) for a in xs]
        if not xs:
            return empty
        return xs[0] if len(xs) == 1 else "ObjectUnionOf(" + " ".join(xs) + ")"

    lines = ["Prefix(:=<http://example.org/c2#>)", "Ontology(<http://example.org/c2>"]
    for a in range(kb.n):
        lines.append(f"Declaration(Class({C(a)}))")
    for r in range(kb.m):
        lines.append(f"Declaration(ObjectProperty({R(2 * r)}))")
    for a in sorted(kb.noms):
        lines.append(f"Declaration(NamedIndividual(:i_{kb.cname(a)}))")
    for cl in kb.clauses:
        k = cl[0]
        if k == "gci":
            lines.append(f"SubClassOf({conj(cl[1], 'owl:Thing')} {disj(cl[2], 'owl:Nothing')})")
        elif k == "ex":
            lines.append(f"SubClassOf({C(cl[1])} ObjectSomeValuesFrom({R(cl[2])} {C(cl[3])}))")
        elif k == "all":
            lines.append(f"SubClassOf({C(cl[1])} ObjectAllValuesFrom({R(cl[2])} {C(cl[3])}))")
        elif k == "ge":
            lines.append(f"SubClassOf({C(cl[1])} ObjectMinCardinality({cl[2]} {R(cl[3])} {C(cl[4])}))")
        elif k == "le":
            lines.append(f"SubClassOf({C(cl[1])} ObjectMaxCardinality({cl[2]} {R(cl[3])} {C(cl[4])}))")
        elif k == "sub":
            lines.append(f"SubObjectPropertyOf({R(cl[1])} {R(cl[2])})")
        elif k == "nom":
            lines.append(f"EquivalentClasses({C(cl[1])} ObjectOneOf(:i_{kb.cname(cl[1])}))")
    lines.append(")")
    return "\n".join(lines) + "\n"
