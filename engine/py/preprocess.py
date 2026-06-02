"""Sound nominal preprocessing for the context-calculus engine.

The engine implements the ALCHIQ context calculus (Table 2).  Nominals are
handled by the *ABox-grounded* reduction below, which is sound: a nominal
concept ``{o}`` (written ``__nom__o`` by the normaliser, with
``hooks.nominal_to_individual[__nom__o] = o``) is true exactly at the individual
``o``.  Hence every assertion ``C(o)`` in the ABox yields the TBox clause

    __nom__o(x) -> C(x)          [ if x = o then C(x) = C(o) = true ]

and every role assertion ``R(o, o')`` with ``o'`` also a nominal individual
yields ``__nom__o(x) -> exists/role …`` we keep to the concept case here
(sufficient for class subsumption through nominals).

This closes nominal subsumptions of the form ``A ⊑ {o} ⊑ C`` (e.g.
``Queen ≡ {Elizabeth}`` with ``Female(Elizabeth)`` gives ``Queen ⊑ Female``).
It does NOT implement the full Table-3 nominal rules (Nom/Join/r-Succ/r-Pred),
which are needed only for nominal/inverse/number-restriction *merge*
interactions; those remain out of scope and are reported, never approximated
unsoundly.
"""
from __future__ import annotations
from moose.sroiq import dlclauses as dlc

X = dlc.X


def nominal_clauses(abox, hooks):
    """Return extra TBox DL-clauses `__nom__o(x) -> C(x)` derived soundly from
    the ABox assertions about nominal individuals."""
    ind_to_nom = {ind: nom for nom, ind in getattr(hooks, "nominal_to_individual", {}).items()}
    extra = []
    for c in abox:
        if c.body:  # only unconditional ABox facts
            continue
        for a in c.head:
            if isinstance(a, dlc.ConceptAtom) and isinstance(a.term, dlc.Individual):
                nom = ind_to_nom.get(a.term.name)
                if nom is not None:
                    extra.append(
                        dlc.DLClause(
                            body=frozenset({dlc.ConceptAtom(nom, X)}),
                            head=frozenset({dlc.ConceptAtom(a.concept, X)}),
                        )
                    )
    return extra


def _is_role(a):
    return isinstance(a, dlc.RoleAtom)


def detect_role_chains(tbox):
    """Detect role chains `R∘S⊑T` from the raw chain clauses the normaliser
    emits: body `{R(a,b), S(b,c)}`, head `T(a,c)` (shared middle `b`), with
    arbitrary variable names.  Returns (transitive_set, chain_triples) where
    `transitive_set = {R : (R∘R⊑R)}` and `chain_triples = [(R,S,T), ...]` for
    the proper (non-transitive) chains."""
    trans = set()
    chains = []
    for c in tbox:
        roles = [a for a in c.body if _is_role(a)]
        heads = list(c.head)
        if len(roles) == 2 and len(c.body) == 2 and len(heads) == 1 and _is_role(heads[0]):
            r0, r1, h = roles[0], roles[1], heads[0]
            # orient: first.target == second.source == middle
            pair = None
            if r0.target == r1.source:
                pair = (r0, r1)
            elif r1.target == r0.source:
                pair = (r1, r0)
            if pair is None:
                continue
            first, second = pair
            if h.source == first.source and h.target == second.target and first.source != second.target:
                if first.role == second.role == h.role:
                    trans.add(h.role)
                else:
                    chains.append((first.role, second.role, h.role))
    return trans, chains


def detect_transitive_roles(tbox):
    return detect_role_chains(tbox)[0]


def transitivity_clauses(tbox):
    """Reachability encoding of transitive roles (the role automaton specialised
    to `R∘R⊑R`).  For a transitive role `R` and each backward clause
    `Γ_x ∧ R(x,y) ∧ ⋀C_i(y) → Δ_x` (a `∃R.(⋀C_i)`-style consequence), introduce
    a reachability concept `P` with

        R(x,y) ∧ ⋀C_i(y) → P(x)        (P ⊇ ∃R.⋀C_i)
        R(x,y) ∧ P(y)     → P(x)        (transitivity: ∃R.P ⊑ P)
        Γ_x ∧ P(x)        → Δ_x         (the consequence, through any R-path)

    Sound: every model of the originals satisfies these (P is interpreted as
    "has an R-path to a ⋀C_i element").  Makes multi-step R consequences
    derivable, which the single-edge clause alone misses under transitivity."""
    trans = detect_transitive_roles(tbox)
    if not trans:
        return []
    extra = []
    seen = {}
    for c in tbox:
        roles = [a for a in c.body if _is_role(a)]
        if len(roles) != 1:
            continue
        r = roles[0]
        if r.role not in trans or r.source != X:
            continue
        y = r.target
        if y == X:
            continue
        c_on_y = sorted(
            a.concept for a in c.body if isinstance(a, dlc.ConceptAtom) and a.term == y
        )
        gamma_x = [a for a in c.body if isinstance(a, dlc.ConceptAtom) and a.term == X]
        # head must be concept(s) on x
        if not c_on_y or not c.head:
            continue
        if not all(isinstance(h, dlc.ConceptAtom) and h.term == X for h in c.head):
            continue
        key = (r.role, tuple(c_on_y))
        p = seen.get(key)
        if p is None:
            p = f"__trans__{r.role}__{'_'.join(c_on_y)}"
            seen[key] = p
            # R(x,y) ∧ ⋀C_i(y) → P(x)
            body1 = {dlc.RoleAtom(r.role, X, y)} | {
                dlc.ConceptAtom(ci, y) for ci in c_on_y
            }
            extra.append(dlc.DLClause(body=frozenset(body1), head=frozenset({dlc.ConceptAtom(p, X)})))
            # R(x,y) ∧ P(y) → P(x)
            extra.append(
                dlc.DLClause(
                    body=frozenset({dlc.RoleAtom(r.role, X, y), dlc.ConceptAtom(p, y)}),
                    head=frozenset({dlc.ConceptAtom(p, X)}),
                )
            )
        # Γ_x ∧ P(x) → Δ_x
        body3 = set(gamma_x) | {dlc.ConceptAtom(p, X)}
        extra.append(dlc.DLClause(body=frozenset(body3), head=frozenset(c.head)))
    return extra


def chain_clauses(tbox):
    """Role-chain encoding for `R∘S⊑T` (R≠S).  For each chain and each axiom
    `∃T.(⋀C_i) ⊑ Δ` (clause `T(x,y) ∧ ⋀C_i(y) → Δ(x)`), add the sound
    central-form clauses

        S(x,w) ∧ ⋀C_i(w) → Q(x)     (Q = ∃S.⋀C_i)
        R(x,y) ∧ Q(y)     → Δ(x)     (an R-succ that is ∃S.⋀C_i gives a T-path)

    Sound because `R(x,y) ∧ S(y,w)` implies `T(x,w)` (the chain), so an
    `R∘S` path to a `⋀C_i` element is a `T`-edge to it, hence `∃T.⋀C_i ⊑ Δ`."""
    _trans, chains = detect_role_chains(tbox)
    if not chains:
        return []
    by_t = {}
    for (r, s, t) in chains:
        by_t.setdefault(t, []).append((r, s))
    extra = []
    seen = {}
    for c in tbox:
        roles = [a for a in c.body if _is_role(a)]
        if len(roles) != 1:
            continue
        tatom = roles[0]
        if tatom.source != X or tatom.target == X or tatom.role not in by_t:
            continue
        y = tatom.target
        c_on_y = sorted(a.concept for a in c.body if isinstance(a, dlc.ConceptAtom) and a.term == y)
        if not c_on_y or not c.head:
            continue
        if not all(isinstance(h, dlc.ConceptAtom) and h.term == X for h in c.head):
            continue
        for (r, s) in by_t[tatom.role]:
            key = (s, tuple(c_on_y))
            q = seen.get(key)
            if q is None:
                q = f"__chain__{s}__{'_'.join(c_on_y)}"
                seen[key] = q
                body1 = {dlc.RoleAtom(s, X, y)} | {dlc.ConceptAtom(ci, y) for ci in c_on_y}
                extra.append(dlc.DLClause(body=frozenset(body1), head=frozenset({dlc.ConceptAtom(q, X)})))
            extra.append(
                dlc.DLClause(
                    body=frozenset({dlc.RoleAtom(r, X, y), dlc.ConceptAtom(q, y)}),
                    head=frozenset(c.head),
                )
            )
    return extra


def _is_chain_axiom(c):
    """True for a raw role-chain / transitivity clause `R(a,b) ∧ S(b,c) → T(a,c)`
    (shared middle `b`), i.e. exactly the clause shape that has a body role with
    no central variable.  These are *replaced* by the central-form reachability /
    chain encoding below, so they must not be passed through to the engine (which
    would otherwise drop them as unsupported)."""
    roles = [a for a in c.body if _is_role(a)]
    heads = list(c.head)
    if len(roles) == 2 and len(c.body) == 2 and len(heads) == 1 and _is_role(heads[0]):
        r0, r1, h = roles[0], roles[1], heads[0]
        pair = (r0, r1) if r0.target == r1.source else \
               (r1, r0) if r1.target == r0.source else None
        if pair is not None:
            first, second = pair
            if (h.source == first.source and h.target == second.target
                    and first.source != second.target):
                return True
    return False


def augment(tbox, abox, hooks):
    """tbox plus: sound nominal clauses, the transitive-role reachability
    encoding (`R∘R⊑R`), and the role-chain encoding (`R∘S⊑T`).

    The raw chain/transitivity axioms are *removed* from the pass-through set:
    they are out of the ALCHIQ clause normal form (body role without a central
    variable) and are fully replaced by the central-form encoding, so the engine
    consumes every emitted clause and drops nothing."""
    tbox = list(tbox)
    base = [c for c in tbox if not _is_chain_axiom(c)]
    return (
        base
        + nominal_clauses(abox, hooks)
        + transitivity_clauses(tbox)
        + chain_clauses(tbox)
    )
