"""Normal form of the sroiq-c2a route, as printed by NFDump.lean.

Roles are encoded as integers: +k -> 2k, -k -> 2k+1, so flip(R) = R ^ 1.
Untrusted tooling for stage H1; the proved checker judges every hint.
"""


def rt(s):
    k = int(s[1:])
    return 2 * k if s[0] == '+' else 2 * k + 1


def rts(r):
    return ('+' if r % 2 == 0 else '-') + str(r // 2)


class Part:
    def __init__(self):
        self.noms = []
        self.gci = []      # (body tuple, head tuple)
        self.ex = []       # (a, R, b)
        self.all = []      # (a, S, c)
        self.ge = []       # (a, k, R, b)
        self.le = []       # (a, k, R, b)
        self.chain = []    # (body roles tuple, S)


class NF:
    def __init__(self):
        self.route = None
        self.n = 0
        self.m = 0
        self.cname = {}    # iri -> index
        self.rname = {}
        self.nominal = {}  # individual iri -> nominal name index
        self.parts = []
        self.error = None


def parse(path):
    nf = NF()
    cur = None
    with open(path) as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            d = w[0]
            if d == 'gci':
                i = w.index('|')
                cur.gci.append((tuple(int(x) for x in w[1:i]), tuple(int(x) for x in w[i + 1:])))
            elif d == 'ex':
                cur.ex.append((int(w[1]), rt(w[2]), int(w[3])))
            elif d == 'all':
                cur.all.append((int(w[1]), rt(w[2]), int(w[3])))
            elif d == 'ge':
                cur.ge.append((int(w[1]), int(w[2]), rt(w[3]), int(w[4])))
            elif d == 'le':
                cur.le.append((int(w[1]), int(w[2]), rt(w[3]), int(w[4])))
            elif d == 'chain':
                i = w.index('|')
                cur.chain.append((tuple(rt(x) for x in w[1:i]), rt(w[i + 1])))
            elif d == 'nom':
                cur.noms.append(int(w[1]))
            elif d == 'part':
                cur = Part()
                nf.parts.append(cur)
            elif d == 'cname':
                nf.cname[w[2]] = int(w[1])
            elif d == 'rname':
                nf.rname[w[2]] = int(w[1])
            elif d == 'nominal':
                nf.nominal[w[2]] = int(w[1])
            elif d == 'n':
                nf.n = int(w[1])
            elif d == 'm':
                nf.m = int(w[1])
            elif d == 'route':
                nf.route = w[1]
            elif d == 'error':
                nf.error = ' '.join(w[1:])
    return nf


class Index:
    """Lookup tables over one part."""

    def __init__(self, nf, part):
        self.n = nf.n
        self.m = nf.m
        self.part = part
        n = nf.n
        self.noms = list(dict.fromkeys(part.noms))
        self.nomset = set(self.noms)
        self.gci = part.gci
        self.gci_by_body = [[] for _ in range(n)]
        self.gci_empty = []
        for g, (b, h) in enumerate(part.gci):
            bs = set(b)
            if not bs:
                self.gci_empty.append(g)
            for a in bs:
                self.gci_by_body[a].append(g)
        self.body_len = [len(set(b)) for (b, h) in part.gci]
        self.ex_by = {}
        for (a, R, b) in part.ex:
            self.ex_by.setdefault(a, []).append((R, b))
        self.all_by = {}
        for (a, S, c) in part.all:
            self.all_by.setdefault(a, []).append((S, c))
        self.ge_by = {}
        for (a, k, R, b) in part.ge:
            self.ge_by.setdefault(a, []).append((k, R, b))
        self.le_by = {}
        for (a, k, R, b) in part.le:
            self.le_by.setdefault(a, []).append((k, R, b))
        # role hierarchy: R <= S for chain [R] S, closed under flip
        nr = 2 * nf.m
        step = [set() for _ in range(nr)]
        self.long_chains = []
        for (body, S) in part.chain:
            if len(body) == 1:
                R = body[0]
                step[R].add(S)
                step[R ^ 1].add(S ^ 1)
            else:
                self.long_chains.append((body, S))
        self.up = []
        for R in range(nr):
            seen = {R}
            st = [R]
            while st:
                x = st.pop()
                for y in step[x]:
                    if y not in seen:
                        seen.add(y)
                        st.append(y)
            self.up.append(frozenset(seen))

    def upL(self, L):
        out = set()
        for R in L:
            out |= self.up[R]
        return frozenset(out)


def from_route(index_text, clauses_text):
    """The normal form of `sroiq-hint` from `--print-index` and
    `--print-clauses` (the same row)."""
    nf = NF()
    nf.route = 'sroiq-hint'
    p = Part()
    nf.parts.append(p)
    for line in index_text.split('\n'):
        w = line.split(' ', 2)
        if w[0] == 'concepts':
            nf.n = int(w[1])
        elif w[0] == 'roles':
            nf.m = int(w[1])
        elif w[0] == 'concept' and len(w) == 3:
            nf.cname[w[2]] = int(w[1])
        elif w[0] == 'role' and len(w) == 3:
            nf.rname[w[2]] = int(w[1])
        elif w[0] == 'nominal' and len(w) == 3:
            nf.nominal[w[2]] = int(w[1])
    nf.data_clauses = 0
    for line in clauses_text.split('\n'):
        w = line.split()
        if not w:
            continue
        d = w[0]
        if d == 'gci':
            i = w.index('->')
            p.gci.append((tuple(int(x) for x in w[1:i]), tuple(int(x) for x in w[i + 1:])))
        elif d == 'some':
            p.ex.append((int(w[1]), rt(w[2]), int(w[3])))
        elif d == 'all':
            p.all.append((int(w[1]), rt(w[2]), int(w[3])))
        elif d == 'atleast':
            p.ge.append((int(w[1]), int(w[2]), rt(w[3]), int(w[4])))
        elif d == 'atmost':
            p.le.append((int(w[1]), int(w[2]), rt(w[3]), int(w[4])))
        elif d == 'chain':
            toks = [x for x in w[1:] if x not in ('->', '|')]
            p.chain.append((tuple(rt(x) for x in toks[:-1]), rt(toks[-1])))
        elif d == 'nom':
            p.noms.append(int(w[1]))
        elif d == 'data-clauses':
            nf.data_clauses = int(w[1])
    return nf
