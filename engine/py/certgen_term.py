#!/usr/bin/env python3
"""Term-algebra certificate generator: validate the actual Rust reasoner's
verdicts against the Lean-verified *term-algebra* checker
(`ContextCalculus.CheckerTerm`).

This supersedes `certgen_fo.py`: where the FO checker encoded a successor as a
one-level term `fₖ(x)`, the term-algebra checker uses a genuine term algebra
`FTerm` (`var i` / `app f t`), so **nested** successors `f(g(x))` are
first-class.  That lets us certify verdicts whose derivation builds a successor
of a successor — transitive-role / successor-chain subsumptions such as
`trans_test`'s `A ⊑ D` and the nested `kinship` subsumptions — which previously
stayed validated only empirically against HermiT.

Per ontology (engine JSON-clause input, or `.ofn` via `frontend.py`):
  1. run the real engine -> verdicts;
  2. re-derive each verdict from the genuine premises.  Two derivation engines,
     tried in order, both emitting steps the verified checker re-checks:
       (a) propositional resolution (no instantiation) -- a fast path;
       (b) complete disjunctive saturation over the term algebra: ground
           resolution over matching-driven instance generation (positive
           hyperresolution).  Rules are instantiated at the successor terms their
           bodies match against the ground atoms already produced (the pool of
           positive consequences, *including disjuncts*); full binary resolution
           then combines the ground clauses, carrying residual disjunctions, and
           Factor equalities feed forward paramodulation.  This handles
           disjunctive heads and nested successors `f(g(x))` together, not just
           Horn; nesting is bounded by a depth limit (the engine itself
           terminates by blocking).
     Engine output is never assumed as an axiom -- every step is a premise
     instance, the context core, resolution, or paramodulation.
  3. emit a Lean file with `certifies_subsumptionT` / `certifies_unsatT`
     theorems proved `by decide` (kernel-checked, `[propext, Quot.sound]`).
"""
from __future__ import annotations
import json, subprocess, sys
from pathlib import Path

CRATE = Path(__file__).resolve().parent.parent
BIN = CRATE / "target" / "release" / "kobayashi-marust"
BOTTOM = {"Nothing", "owl:Nothing", "⊥"}

MAXDEPTH = 5          # max successor-nesting depth for forward chaining
MAX_ROUNDS = 40       # forward-chaining rounds
MAX_PROP_STEPS = 60000
MAX_CLAUSES = 50000   # cap for the disjunctive fallback (bounded, may give up)

# ---------------------------------------------------------------------------
# Term-tree interner.  Terms: ('V', int) variable/constant; ('A', fn, arg).
# Atoms: ('c', cid, t) | ('r', rid, s, t) | ('e', s, t).
# Clauses: (frozenset(body), frozenset(head)).
# ---------------------------------------------------------------------------

class Interner:
    def __init__(self):
        self.concept = {}
        self.role = {}
        self.fn = {}
        self.neg = {}
        self.varcodes = {0}   # ids that are universally-quantifiable variables

    def cc(self, n): return self.concept.setdefault(n, len(self.concept) + 1)
    def rc(self, n): return self.role.setdefault(n, len(self.role) + 1)

    def tc(self, t):
        if t["kind"] == "var":
            if t["name"] == "x":
                return ("V", 0)
            key = ("v", t["name"])
            if key not in self.neg:
                self.neg[key] = -(len(self.neg) + 2)   # neighbour variable
                self.varcodes.add(self.neg[key])
            return ("V", self.neg[key])
        if t["kind"] == "fun":
            f = t["function"]
            if f not in self.fn:
                self.fn[f] = len(self.fn) + 1
            return ("A", self.fn[f], self.tc(t["arg"]))   # recurse: nested terms
        # individual / constant: a fixed *non-variable* negative id
        key = ("k", json.dumps(t, sort_keys=True))
        if key not in self.neg:
            self.neg[key] = -(1000 + len(self.neg))
        return ("V", self.neg[key])

    def atom(self, a):
        if a["kind"] == "concept":
            return ("c", self.cc(a["concept"]), self.tc(a["term"]))
        if a["kind"] == "role":
            return ("r", self.rc(a["role"]), self.tc(a["source"]), self.tc(a["target"]))
        if a["kind"] == "eq":
            return ("e", self.tc(a["left"]), self.tc(a["right"]))
        raise ValueError(a)


def canon(body, head):
    return (frozenset(body), frozenset(head))


# ---------------------------------------------------------------------------
# Term operations
# ---------------------------------------------------------------------------

def depth(t):
    return 0 if t[0] == "V" else 1 + depth(t[2])


def maximal_head(head):
    """The head literals on a maximal-depth term -- the ones the (ordered)
    calculus resolves on.  In the context literal ordering a literal on a
    successor term f(x) is larger than one on the central/predecessor variable,
    so disjuncts about a successor are peeled off first; this both mirrors the
    engine's max-head selection and keeps the disjunctive saturation bounded
    (resolving on every disjunct indiscriminately is what blows up and yields a
    false fixpoint).  When all disjuncts sit on the same depth (e.g. a purely
    central-variable clause) every literal is maximal, so plain ALC reasoning is
    unaffected.  Ordered positive hyperresolution stays refutation-complete, so
    no derivable verdict is lost (verified: 0 uncovered across the suite)."""
    if not head:
        return head
    m = max(max(depth(t) for t in atom_terms(a)) for a in head)
    return [a for a in head if max(depth(t) for t in atom_terms(a)) == m]


def subst_term(t, s):
    if t[0] == "V":
        return s.get(t[1], t)
    return ("A", t[1], subst_term(t[2], s))


def subst_atom(a, s):
    if a[0] == "c": return ("c", a[1], subst_term(a[2], s))
    if a[0] == "r": return ("r", a[1], subst_term(a[2], s), subst_term(a[3], s))
    return ("e", subst_term(a[1], s), subst_term(a[2], s))


def subst_clause(c, s):
    b, h = c
    return canon([subst_atom(a, s) for a in b], [subst_atom(a, s) for a in h])


def match_term(pat, gr, sub, varcodes):
    if pat[0] == "V":
        if pat[1] in varcodes:                 # a rule variable (incl. x = 0)
            if pat[1] in sub:
                return sub if sub[pat[1]] == gr else None
            s = dict(sub); s[pat[1]] = gr; return s
        return sub if pat == gr else None       # a constant: must be equal
    if gr[0] != "A" or gr[1] != pat[1]:
        return None
    return match_term(pat[2], gr[2], sub, varcodes)


def match_atom(pat, fact, sub, varcodes):
    if pat[0] != fact[0]:
        return None
    if pat[0] == "c":
        if pat[1] != fact[1]: return None
        return match_term(pat[2], fact[2], sub, varcodes)
    if pat[0] == "r":
        if pat[1] != fact[1]: return None
        s2 = match_term(pat[2], fact[2], sub, varcodes)
        if s2 is None: return None
        return match_term(pat[3], fact[3], s2, varcodes)
    s2 = match_term(pat[1], fact[1], sub, varcodes)
    if s2 is None: return None
    return match_term(pat[2], fact[2], s2, varcodes)


def resolvent(c1, c2, a):
    b1, h1 = c1; b2, h2 = c2
    return canon(b1 | (b2 - {a}), (h1 - {a}) | h2)


def rwT(s, t, u):
    if u == s: return t
    if u[0] == "A": return ("A", u[1], rwT(s, t, u[2]))
    return u


def rwL(s, t, L):
    if L[0] == "c": return ("c", L[1], rwT(s, t, L[2]))
    if L[0] == "r": return ("r", L[1], rwT(s, t, L[2]), rwT(s, t, L[3]))
    return ("e", rwT(s, t, L[1]), rwT(s, t, L[2]))


def para_resolvent(c1, c2, s, t, L):
    b1, h1 = c1; b2, h2 = c2
    return canon(b1 | b2, {rwL(s, t, L)} | (h1 - {("e", s, t)}) | (h2 - {L}))


# ---------------------------------------------------------------------------
# Derivation bookkeeping (shared by both engines)
# ---------------------------------------------------------------------------

class Deriv:
    def __init__(self):
        self.order = []
        self.just = []
        self.index = {}

    def add(self, c, j):
        if c in self.index:
            return self.index[c]
        self.index[c] = len(self.order)
        self.order.append(c); self.just.append(j)
        return self.index[c]

    def prune(self, tgt_idx):
        needed, stack = set(), [tgt_idx]
        while stack:
            k = stack.pop()
            if k in needed: continue
            needed.add(k)
            j = self.just[k]
            if j[0] in ("res", "para"):
                stack.extend([j[1], j[2]])
        keep = sorted(needed)
        remap = {old: new for new, old in enumerate(keep)}
        out = []
        for old in keep:
            c, j = self.order[old], self.just[old]
            if j[0] == "res":
                out.append((c, ("res", remap[j[1]], remap[j[2]], j[3])))
            elif j[0] == "para":
                out.append((c, ("para", remap[j[1]], remap[j[2]], j[3], j[4], j[5])))
            else:
                out.append((c, j))
        return out


# ---------------------------------------------------------------------------
# Engine (a): propositional resolution (no instantiation) -- disjunctive core
# ---------------------------------------------------------------------------

def derive_prop(prem_list, core, target):
    D = Deriv()
    for c, i in prem_list:
        D.add(c, ("prem", i, {}))
    D.add(core, ("core",))
    if target in D.index:
        return D.prune(D.index[target])
    steps = 0
    changed = True
    while changed:
        changed = False
        n = len(D.order)
        for i in range(n):
            c1 = D.order[i]
            for j in range(n):
                c2 = D.order[j]
                for a in (c1[1] & c2[0]):
                    steps += 1
                    if steps > MAX_PROP_STEPS:
                        return None
                    res = resolvent(c1, c2, a)
                    if res in D.index:
                        continue
                    k = D.add(res, ("res", i, j, a))
                    changed = True
                    if res == target:
                        return D.prune(k)
    return None


# ---------------------------------------------------------------------------
# Engine (b): complete disjunctive saturation over the term algebra
#
# Ground resolution over matching-driven instance generation -- i.e. positive
# hyperresolution lifted to the term algebra.  This handles *disjunctive* heads
# and *nested* successors together (not just Horn): a premise rule is
# instantiated at the successor terms its body atoms match against the ground
# atoms already produced (the "pool" of positive consequences -- including
# disjuncts), and full binary resolution then combines the resulting ground
# clauses, carrying residual disjunctions.  Equalities (Factor) feed forward
# paramodulation.  Completeness rests on: (i) positive hyperresolution is
# refutation-complete for first-order clauses, and (ii) the engine's blocking
# bounds the successor depth, so a finite term-instantiation suffices (we cap it
# at MAXDEPTH, mirroring blocking).
# ---------------------------------------------------------------------------

def atom_terms(a):
    if a[0] == "c": return [a[2]]
    if a[0] == "r": return [a[2], a[3]]
    return [a[1], a[2]]


def term_ground(t, varcodes):
    """Ground = no neighbour variable; the root ('V',0) and constants are ground."""
    if t[0] == "V":
        return t[1] == 0 or t[1] not in varcodes
    return term_ground(t[2], varcodes)


def atom_ground(a, varcodes):
    return all(term_ground(t, varcodes) for t in atom_terms(a))


def clause_ground(c, varcodes):
    return all(atom_ground(a, varcodes) for a in (list(c[0]) + list(c[1])))


def clause_depth_ok(c):
    return all(depth(t) <= MAXDEPTH for a in (list(c[0]) + list(c[1]))
               for t in atom_terms(a))


def head_pool(D, varcodes):
    """Ground atoms appearing in the head of a positive consequence (empty body)
    -- the electrons available for hyperresolution (disjuncts included)."""
    pool = set()
    for c in D.order:
        if len(c[0]) == 0:
            for a in c[1]:
                if atom_ground(a, varcodes):
                    pool.add(a)
    return pool


def all_matches(body, pool, varcodes):
    """All substitutions making every body atom equal to some pool atom."""
    subs = [{}]
    for ba in body:
        new = []
        for sub in subs:
            for fa in pool:
                s2 = match_atom(ba, fa, sub, varcodes)
                if s2 is not None:
                    new.append(s2)
        subs = new
        if not subs:
            return []
    # dedup substitutions
    seen, out = set(), []
    for s in subs:
        key = tuple(sorted(s.items()))
        if key not in seen:
            seen.add(key); out.append(s)
    return out


def positive_consequences(D, varcodes):
    """Ground clauses with empty body -- the electrons for hyperresolution."""
    return [(c, k) for k, c in enumerate(D.order)
            if len(c[0]) == 0 and clause_ground(c, varcodes)]


def unit_atoms(D, varcodes):
    """Map atom -> index for ground *unit* consequences ([]->[atom])."""
    out = {}
    for k, c in enumerate(D.order):
        if len(c[0]) == 0 and len(c[1]) == 1 and clause_ground(c, varcodes):
            out[next(iter(c[1]))] = k
    return out


def derive_horn(prem_list, core, target, varcodes):
    """Unit-driven Horn forward chaining over the term algebra: fire a Horn rule
    (single head) when all its body atoms match ground *unit* consequences,
    instantiating it at the matched successor terms; Factor equalities feed
    forward paramodulation.  Efficient (no disjunctive blow-up) and the right
    engine for the vast majority of classification queries.  Refutation of a
    genuinely disjunctive query is left to `derive_full`."""
    D = Deriv()
    schemas = []
    for c, i in prem_list:
        D.add(c, ("prem", i, {}))
        if len(c[0]) > 0:
            schemas.append((c, i))
    D.add(core, ("core",))
    if target in D.index:
        return D.prune(D.index[target])

    for _ in range(MAX_ROUNDS):
        changed = False
        units = unit_atoms(D, varcodes)
        upool = set(units.keys())
        for c, i in schemas:
            if len(c[1]) > 1:
                continue                                  # Horn rules only
            for sub in all_matches(list(c[0]), upool, varcodes):
                inst = subst_clause(c, sub)
                if not clause_ground(inst, varcodes) or not clause_depth_ok(inst):
                    continue
                # skip when the *consequence* is already derived (the instance
                # itself may coincide with a var-rooted schema clause).
                if canon([], inst[1]) in D.index:
                    continue
                pairs = {k: v for k, v in sub.items() if ("V", k) != v}
                cidx = D.index.get(inst) if inst in D.index \
                    else D.add(inst, ("prem", i, pairs))
                cur, ok = inst, True
                for ba in list(inst[0]):
                    if ba not in units:
                        ok = False; break
                    fidx = units[ba]
                    res = resolvent(D.order[fidx], cur, ba)
                    cidx = D.add(res, ("res", fidx, cidx, ba)); cur = res
                if not ok:
                    continue
                changed = True
                if cur == target:
                    return D.prune(cidx)
        # forward paramodulation on unit eq consequences
        units = unit_atoms(D, varcodes)
        eqs = [(a, ix) for a, ix in units.items() if a[0] == "e" and a[1] != a[2]]
        for (ea, eidx) in eqs:
            s, t = ea[1], ea[2]
            for (la, lidx) in list(units.items()):
                if la[0] == "e":
                    continue
                L2 = rwL(s, t, la)
                if L2 == la:
                    continue
                pc = canon([], [L2])
                if pc in D.index or not clause_depth_ok(pc):
                    continue
                kk = D.add(pc, ("para", eidx, lidx, s, t, la))
                changed = True
                if pc == target:
                    return D.prune(kk)
        if target in D.index:
            return D.prune(D.index[target])
        if not changed:
            break
    return None


def derive_full(prem_list, core, target, varcodes):
    D = Deriv()
    schemas = []
    for c, i in prem_list:
        D.add(c, ("prem", i, {}))          # raw premise (template + var-rooted instance)
        if len(c[0]) > 0:
            schemas.append((c, i))         # rules with a body drive instantiation
    D.add(core, ("core",))
    if target in D.index:
        return D.prune(D.index[target])

    for _ in range(MAX_ROUNDS):
        if len(D.order) > MAX_CLAUSES:
            return None                       # disjunctive blow-up: give up (bounded)
        changed = False
        pool = head_pool(D, varcodes)
        # (1) instance generation: instantiate each rule at terms its body matches
        for c, i in schemas:
            body, _ = c
            for sub in all_matches(list(body), pool, varcodes):
                inst = subst_clause(c, sub)
                if inst in D.index or not clause_ground(inst, varcodes) \
                        or not clause_depth_ok(inst):
                    continue
                pairs = {k: v for k, v in sub.items() if ("V", k) != v}
                D.add(inst, ("prem", i, pairs))
                changed = True
        # (2) positive hyperresolution: resolve the body atoms of every ground
        #     rule-instance against positive consequences (electrons), carrying
        #     residual disjunctions.  Targeted (rule x consequence), so the
        #     disjunctive search stays bounded; complete for refutation.
        steps = 0
        more = True
        while more:
            more = False
            # Electrons resolve only on their *maximal* head literal (ordered
            # positive hyperresolution); this prunes the disjunctive blow-up.
            cons_by_atom = {}
            for el, elidx in positive_consequences(D, varcodes):
                for a in maximal_head(el[1]):
                    cons_by_atom.setdefault(a, []).append((el, elidx))
            rules = [(c, k) for k, c in enumerate(D.order)
                     if len(c[0]) > 0 and clause_ground(c, varcodes)]
            for cur, cidx in rules:
                if steps > MAX_PROP_STEPS:
                    break
                for ba in list(cur[0]):
                    if steps > MAX_PROP_STEPS:
                        break
                    for el, elidx in cons_by_atom.get(ba, []):
                        res = resolvent(el, cur, ba)
                        if not clause_depth_ok(res) or res in D.index:
                            continue
                        # Count the *budget* against productive steps (clauses
                        # actually added), not against redundant re-derivations:
                        # otherwise a large set of already-known resolvents
                        # exhausts the budget and the search reports a spurious
                        # fixpoint while genuinely new clauses remain reachable.
                        steps += 1
                        k = D.add(res, ("res", elidx, cidx, ba))
                        changed = more = True
                        if res == target:
                            return D.prune(k)
                        if len(D.order) > MAX_CLAUSES or steps > MAX_PROP_STEPS:
                            more = False; break
        # (3) forward paramodulation: a unit eq consequence (s≈t) rewrites s->t
        cons = [(next(iter(c[1])), k) for k, c in enumerate(D.order)
                if len(c[0]) == 0 and len(c[1]) == 1 and clause_ground(c, varcodes)]
        eqs = [(a, ix) for a, ix in cons if a[0] == "e" and a[1] != a[2]]
        for (ea, eidx) in eqs:
            s, t = ea[1], ea[2]
            for (la, lidx) in cons:
                if la[0] == "e":
                    continue
                L2 = rwL(s, t, la)
                if L2 == la:
                    continue
                pc = canon([], [L2])
                if pc in D.index or not clause_depth_ok(pc):
                    continue
                kk = D.add(pc, ("para", eidx, lidx, s, t, la))
                changed = True
                if pc == target:
                    return D.prune(kk)
        if target in D.index:
            return D.prune(D.index[target])
        if not changed:
            break
    return None


# ---------------------------------------------------------------------------
# Lean emission
# ---------------------------------------------------------------------------

def emit_t(t):
    if t[0] == "V":
        return f"(FTerm.var ({t[1]}))"
    return f"(FTerm.app {t[1]} {emit_t(t[2])})"


def emit_lit(L):
    if L[0] == "c":
        return f"FLit.P (FPred.concept {L[1]} {emit_t(L[2])})"
    if L[0] == "r":
        return f"FLit.P (FPred.role {L[1]} {emit_t(L[2])} {emit_t(L[3])})"
    return f"FLit.eq {emit_t(L[1])} {emit_t(L[2])}"


def emit_clause(c):
    b, h = c
    bs = ", ".join(emit_lit(k) for k in sorted(b))
    hs = ", ".join(emit_lit(k) for k in sorted(h))
    return f"⟨[{bs}], [{hs}]⟩"


def emit_sub(s):
    pairs = [(k, v) for k, v in sorted(s.items()) if ("V", k) != v]
    return "[" + ", ".join(f"(({k}), {emit_t(v)})" for k, v in pairs) + "]"


def emit_just(j):
    if j[0] == "core": return ".core"
    if j[0] == "prem": return f".prem {j[1]} {emit_sub(j[2])}"
    if j[0] == "para":
        return f".para {j[1]} {j[2]} {emit_t(j[3])} {emit_t(j[4])} ({emit_lit(j[5])})"
    return f".res {j[1]} {j[2]} ({emit_lit(j[3])})"


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def run_engine(clauses):
    proc = subprocess.run([str(BIN)], input=json.dumps({"clauses": clauses}),
                          capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr)
    return json.loads(proc.stdout)


def short(n): return n.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def is_internal(name: str) -> bool:
    s = short(name)
    return s.startswith("Q_") or s.startswith("__") or s.startswith("aux_") \
        or s.startswith("def_") or (":" in s and s not in BOTTOM)


def re_derive(prem_list, core, target, varcodes):
    # Layered, in increasing power / cost:
    #  (a) propositional resolution (no instantiation) -- a fast path;
    #  (b) unit-driven Horn forward chaining over the term algebra -- handles
    #      the overwhelming majority of (sub-)consequences efficiently;
    #  (c) the complete disjunctive saturation over the term algebra -- the
    #      completeness fallback for verdicts needing disjunctive case-splitting
    #      *and* nested successors together (bounded, so it may give up).
    return (derive_prop(prem_list, core, target)
            or derive_horn(prem_list, core, target, varcodes)
            or derive_full(prem_list, core, target, varcodes))


def generate(name, input_path, out_path):
    if str(input_path).endswith(".ofn") or str(input_path).endswith(".owl"):
        import frontend
        clauses = frontend.ofn_to_clauses(input_path)
    else:
        clauses = json.loads(Path(input_path).read_text())["clauses"]
    out = run_engine(clauses)
    intern = Interner()
    prem = [canon([intern.atom(a) for a in c["body"]],
                  [intern.atom(a) for a in c["head"]]) for c in clauses]
    prem_list = [(c, i) for i, c in enumerate(prem)]

    verdicts = []
    for a, sups in out["subsumptions"].items():
        if is_internal(a):
            continue
        for s in sups:
            if short(s) in BOTTOM:
                verdicts.append(("unsat", a, None))
            elif not is_internal(s):
                verdicts.append(("sub", a, s))

    L = []
    L.append("-- AUTO-GENERATED by certgen_term.py: kernel-checked validation of the")
    L.append(f"-- Rust reasoner's verdicts on `{name}` against ContextCalculus.CheckerTerm.")
    L.append("import ContextCalculus.CheckerTerm")
    L.append("open ContextCalculus ContextCalculus.CheckerTerm")
    L.append("set_option maxRecDepth 8000")
    L.append("")
    L.append(f"def O_{name} : List FCL := [{', '.join(emit_clause(c) for c in prem)}]")
    L.append("")

    certified, uncovered = [], []
    idx = 0
    for kind, A, B in verdicts:
        Ac = intern.cc(A)
        core = canon([], [("c", Ac, ("V", 0))])
        target = canon([], [] if kind == "unsat" else [("c", intern.cc(B), ("V", 0))])
        cert = re_derive(prem_list, core, target, intern.varcodes)
        if cert is None:
            uncovered.append((kind, A, B)); continue
        body = ",\n    ".join(f"({emit_clause(c)}, {emit_just(j)})" for c, j in cert)
        cn = f"cert_{name}_{idx}"
        L.append(f"def {cn} : List (FCL × JustifT) :=")
        L.append(f"  [ {body} ]")
        if kind == "sub":
            Bc = intern.cc(B)
            thm = f"{name}_{idx}_{short(A)}_sub_{short(B)}"
            L.append(f"theorem {thm} {{D : Type}} (M : TModel D) "
                     f"(hO : ∀ p ∈ O_{name}, valid M p) (a0 : D) "
                     f"(hA : M.conc {Ac} a0) : M.conc {Bc} a0 :=")
            L.append(f"  certifies_subsumptionT O_{name} {Ac} {Bc} {cn} (by decide) M hO a0 hA")
            certified.append(f"{short(A)} ⊑ {short(B)}")
        else:
            thm = f"{name}_{idx}_{short(A)}_unsat"
            L.append(f"theorem {thm} {{D : Type}} (M : TModel D) "
                     f"(hO : ∀ p ∈ O_{name}, valid M p) (a0 : D) : ¬ M.conc {Ac} a0 :=")
            L.append(f"  certifies_unsatT O_{name} {Ac} {cn} (by decide) M hO a0")
            certified.append(f"{short(A)} ⊑ ⊥")
        L.append("")
        idx += 1

    Path(out_path).write_text("\n".join(L) + "\n")
    return certified, uncovered


if __name__ == "__main__":
    name, inp, outp = sys.argv[1], sys.argv[2], sys.argv[3]
    cert, unc = generate(name, inp, outp)
    print(f"[{name}] certified {len(cert)}: " + ", ".join(cert))
    if unc:
        print(f"[{name}] uncovered {len(unc)}: "
              + ", ".join(f"{short(a)}⊑{short(b) if b else '⊥'}" for _, a, b in unc))
