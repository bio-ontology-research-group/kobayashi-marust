#!/usr/bin/env python3
"""Convert moose CB DL-clauses (pre-Skolemized, on stdin as {"clauses":[...]}) into
HT-clauses for the Rust hypertableau (`tableau_cli`), emitting a TInput JSON on
stdout. Reuses the entire moose normalisation pipeline; the only transform is
*reverse Skolemization*: a function symbol `f` introduced by `Body → r(x,f(x))`
plus `Body → C_i(f(x))` becomes the HT existential `Body → ∃r.fil(x)`.

ALCQ + RBox fragment (M2): concept/¬concept, ⊓ (via definers), ⊔ (disjunctive
heads), ∀ (guarded y), ∃ (≥1, via reverse Skolemization), and qualified number
restrictions. ``≥n R.C`` is emitted as n existentials with pairwise-disjoint
fresh *slot* fillers (reuses the ∃ machinery; the disjointness forces n distinct
successors with no separate inequality relation), driven by moose's
``q ∧ ≈(fᵢ,fⱼ) → ⊥`` distinctness constraints. ``≤n R.C`` and functional /
inverse-functional roles are emitted with an ``eq`` head atom that the tableau
discharges by *merging* the two nodes. Nominals (``{a}``) are surfaced as a
fenced record (the singleton semantics needs the merge-into-root machinery, not
yet built) rather than silently passed through as a free concept name. Anything
else (function terms in bodies, equalities we do not recognise) is DROPPED and
counted, never silently approximated.
"""
import json, sys, os


def short(n):
    return n.rsplit("#", 1)[-1].rsplit("/", 1)[-1]


def is_internal(n):
    s = short(n)
    return (s.startswith("Q_") or s.startswith("__") or s.startswith("aux_")
            or s.startswith("def_") or (":" in s and s not in ("Nothing", "owl:Nothing")))


BOTTOM = {"Nothing", "owl:Nothing"}


def is_bottom(n):
    return short(n) in BOTTOM


def _pos_concepts(atoms):
    """If `atoms` are ALL positive concept atoms over a single variable, return
    their concept ids; else None. (Used to recognise excluded-middle /
    disjointness clauses, which are over the root var x.)"""
    out, var = [], None
    for a in atoms:
        if a.get("k") != "c" or a.get("neg"):
            return None
        if var is None:
            var = a["t"]
        elif a["t"] != var:
            return None
        out.append(a["c"])
    return out


def _sub_atom(a, sub):
    """Replace an eliminated concept id by the negation of its complement
    (B := ¬A): flip the literal's polarity. Non-concept atoms pass through."""
    if a.get("k") == "c" and a["c"] in sub:
        return {"k": "c", "neg": not a.get("neg", False), "c": sub[a["c"]], "t": a["t"]}
    return a


def elim_complements(ht_clauses, con_names):
    """KM_HT_EMELIM — sound+complete excluded-middle elimination for the HT path.

    A complementary definer pair shows up as TWO clauses: ``⊤ ⊑ A ∨ B`` (empty
    body, two positive concepts) and ``A ⊓ B ⊑ ⊥`` (two positive concepts, empty
    head). Together these entail ``B ≡ ¬A`` (exactly one of A,B holds). KM's
    clausifier names the negation of a (complex) concept as a fresh definer B and
    then forces the excluded middle ``⊤ ⊑ A ∨ B`` as a disjunction that fires AND
    branches on EVERY node — the cause of the HT model blow-up on the live-∀+⊔
    family (HermiT keeps the negation implicit and never branches A∨¬A).

    Substituting ``B := ¬A`` everywhere and dropping the two now-tautologous
    clauses (``⊤⊑A∨¬A`` and ``A⊓¬A⊑⊥``) is model-preserving, hence sound AND
    complete. We eliminate the internal (definer) side so named/query concepts
    survive, and never eliminate a concept used as an existential filler (its
    ``∃r.B`` occurrence cannot carry the ¬A rewrite)."""
    em, dj = {}, set()
    protected = set()
    for c in ht_clauses:
        for a in c["body"] + c["head"]:
            if a.get("k") == "e":
                protected.add(a["c"])          # existential filler concept
        if not c["body"]:
            h = _pos_concepts(c["head"])
            if h and len(h) == 2 and h[0] != h[1]:
                em[frozenset(h)] = True
        if not c["head"]:
            b = _pos_concepts(c["body"])
            if b and len(b) == 2 and b[0] != b[1]:
                dj.add(frozenset(b))
    pairs = [p for p in em if p in dj]
    if not pairs:
        return ht_clauses, 0

    def internal(i):
        return is_internal(con_names[i])

    sub, used = {}, set()
    for p in pairs:
        a, b = sorted(p)
        if internal(b) and not internal(a):
            elim, keep = b, a
        elif internal(a) and not internal(b):
            elim, keep = a, b
        else:
            elim, keep = b, a            # both internal/named: drop the larger id
        if elim in protected:
            continue                     # would break an ∃r.elim occurrence
        if elim in used or keep in used:
            continue                     # keep substitution chain-free
        sub[elim] = keep
        used.add(elim)
        used.add(keep)
    if not sub:
        return ht_clauses, 0
    elim_pairs = {frozenset((e, k)) for e, k in sub.items()}
    out = []
    for c in ht_clauses:
        if not c["body"]:
            h = _pos_concepts(c["head"])
            if h and len(h) == 2 and frozenset(h) in elim_pairs:
                continue                 # drop ⊤⊑A∨B
        if not c["head"]:
            b = _pos_concepts(c["body"])
            if b and len(b) == 2 and frozenset(b) in elim_pairs:
                continue                 # drop A⊓B⊑⊥
        out.append({"body": [_sub_atom(a, sub) for a in c["body"]],
                    "head": [_sub_atom(a, sub) for a in c["head"]]})
    return out, len(sub)


def convert(clauses, rbox=None, named=None):
    """Convert moose CB clauses (+ optional RBox records from frontend.ofn_rbox)
    into a TInput dict for the Rust tableau. RBox in-fragment records (subrole,
    domain, range) are emitted as HT-clauses; fenced records are surfaced so the
    caller can flag the ontology out-of-fragment (never silently dropped).

    `named` is the set of declared concept names from the frontend. A declared
    class is ALWAYS a query, even when its local name happens to start with an
    "internal-looking" prefix (Q_/__/aux_/def_) or contains ':' — e.g. real
    classes Q_minus, Q_plus, Q_Fever. Without this escape such classes were
    silently excluded from the query set and never classified (HT looked
    incomplete on pure-Horn taxonomies that merely use Q_-prefixed names)."""
    named_set = set(named or [])
    con_names, con_id = [], {}
    rol_names, rol_id = [], {}

    def cid(n):
        if n not in con_id:
            con_id[n] = len(con_names)
            con_names.append(n)
        return con_id[n]

    def rid(n):
        if n not in rol_id:
            rol_id[n] = len(rol_names)
            rol_names.append(n)
        return rol_id[n]

    def term_fun(t):
        return t.get("kind") == "fun"

    def fun_sym(t):
        # f(x) only (arg must be var x); else None
        if t.get("kind") == "fun" and t["arg"].get("kind") == "var" and t["arg"]["name"] == "x":
            return t["function"]
        return None

    # variable numbering per clause: x->0, others 1,2,...
    def mk_varmap():
        return {"x": 0}

    def vnum(name, vm):
        if name not in vm:
            vm[name] = max(vm.values()) + 1 if vm else 0
        return vm[name]

    dropped = 0
    ht_clauses = []          # emitted HT-clauses (dicts with body/head JAtom)
    # reverse-Skolemization accumulator: fsym -> {"body":..., "role":r, "fillers":[c...], "ok":bool}
    exj = {}

    def atom_has_fun(a):
        if a["kind"] == "concept":
            return term_fun(a["term"])
        if a["kind"] == "role":
            return term_fun(a["source"]) or term_fun(a["target"])
        return True  # eq / unknown -> treat as non-ALC

    # ---- pass 1: collect existential-introduction clauses by function symbol ----
    passthrough = []
    eq_clauses = []          # function-free clauses with an eq head (≤n / functional)
    distinct_pairs = []      # (fᵢ, fⱼ) Skolem functions forced pairwise-distinct (≥n)

    def eq_fun_pair(a):
        # f(x) ≈ g(x) between two Skolem function terms -> (f, g), else None.
        if a["kind"] != "eq":
            return None
        fi, fj = fun_sym(a["left"]), fun_sym(a["right"])
        if fi is not None and fj is not None:
            return (fi, fj)
        return None

    for c in clauses:
        body, head = c["body"], c["head"]
        # function symbols appearing in the head
        head_funs = set()
        for a in head:
            if a["kind"] == "concept" and term_fun(a["term"]):
                head_funs.add(fun_sym(a["term"]))
            elif a["kind"] == "role":
                for t in (a["source"], a["target"]):
                    if term_fun(t):
                        head_funs.add(fun_sym(t))
        head_funs.discard(None)
        if head_funs:
            # existential-introduction clause: body must be function-free, head all on one f
            if any(atom_has_fun(a) for a in body) or len(head_funs) != 1:
                dropped += 1
                continue
            f = head_funs.pop()
            rec = exj.setdefault(f, {"body": body, "role": None, "fillers": [], "ok": True})
            for a in head:
                if a["kind"] == "role" and fun_sym(a["target"]) == f and a["source"].get("name") == "x":
                    if rec["role"] is not None and rec["role"] != a["role"]:
                        rec["ok"] = False
                    rec["role"] = a["role"]
                elif a["kind"] == "concept" and fun_sym(a["term"]) == f:
                    rec["fillers"].append(a["concept"])
                else:
                    rec["ok"] = False  # f(x) in unexpected position (e.g. inverse r(f(x),x))
            continue
        # ---- no head function symbols ----
        body_eq_pairs = [p for a in body if (p := eq_fun_pair(a)) is not None]
        if body_eq_pairs and not head:
            # ≥n distinctness: q(x) ∧ ≈(fᵢ(x), fⱼ(x)) → ⊥. Captured by the
            # disjoint-slot encoding below; consume (do NOT count as dropped).
            distinct_pairs.extend(body_eq_pairs)
        elif any(atom_has_fun(a) for a in body):
            # other function term in a body -> outside the fragment
            dropped += 1
        elif any(a["kind"] == "eq" for a in head + body):
            # function-free clause carrying an equality (≤n, functional,
            # inverse-functional): emit with an eq atom -> tableau merge.
            eq_clauses.append(c)
        else:
            passthrough.append(c)

    # functions that must be kept distinct get a fresh per-function slot concept;
    # the slots of a distinctness pair are made disjoint, so the two successors
    # they generate can never be merged by a ≤-rule.
    funcs_needing_slot = set()
    for fi, fj in distinct_pairs:
        funcs_needing_slot.add(fi)
        funcs_needing_slot.add(fj)

    # ---- emit existentials ----
    def jconcept(neg, cn, var):
        return {"k": "c", "neg": neg, "c": cid(cn), "t": var}

    # ---- parse the RBox into maps (used both here and for edge clauses) ----
    # subrole pairs, plus domain/range concept lists keyed by role name; fenced
    # records are surfaced (never silently dropped).
    fenced = []
    subrole_pairs = []
    inverse_pairs = []
    domains, ranges = {}, {}
    for ax in (rbox or []):
        if ax[0] == "subrole":
            subrole_pairs.append((ax[1], ax[2]))
        elif ax[0] == "inverse":
            inverse_pairs.append((ax[1], ax[2]))
        elif ax[0] == "domain":
            domains.setdefault(ax[1], []).append(ax[2])
        elif ax[0] == "range":
            ranges.setdefault(ax[1], []).append(ax[2])
        elif ax[0] == "fenced":
            fenced.append({"reason": ax[1], "detail": ax[2]})
        else:
            fenced.append({"reason": "unknown-rbox", "detail": str(ax)})

    # reflexive-transitive super-role closure: supers[r] = {r} ∪ {s : r ⊑* s}.
    # Domain of a super-role applies to any node carrying a sub-role obligation,
    # so existential-introduction clauses must assert it (blocked nodes never
    # realise the edge, so the edge clause alone would miss them).
    supers = {}

    def super_roles(r):
        if r in supers:
            return supers[r]
        seen, frontier = {r}, [r]
        while frontier:
            cur = frontier.pop()
            for sub, sup in subrole_pairs:
                if sub == cur and sup not in seen:
                    seen.add(sup)
                    frontier.append(sup)
        supers[r] = seen
        return seen

    for f, rec in exj.items():
        if not rec["ok"] or rec["role"] is None or not rec["fillers"]:
            dropped += 1
            continue
        vm = mk_varmap()
        bod = []
        bad = False
        for a in rec["body"]:
            if a["kind"] == "concept" and a["term"].get("kind") == "var":
                bod.append(jconcept(False, a["concept"], vnum(a["term"]["name"], vm)))
            elif a["kind"] == "role" and a["source"].get("kind") == "var" and a["target"].get("kind") == "var":
                bod.append({"k": "r", "r": rid(a["role"]),
                            "s": vnum(a["source"]["name"], vm), "t": vnum(a["target"]["name"], vm)})
            else:
                bad = True
        if bad:
            dropped += 1
            continue
        fillers = list(rec["fillers"])
        if f in funcs_needing_slot:
            fillers.append("__slot__%s" % f)   # disjoint marker -> forces ≥n distinctness
        if len(fillers) == 1 and not is_bottom(fillers[0]):
            fil = cid(fillers[0])
        else:
            # fresh definer D with D ⊑ ⊓ fillers  (D(x) -> C_i(x))
            dname = "def_exfil_%s" % f
            fil = cid(dname)
            for cn in fillers:
                if is_bottom(cn):
                    ht_clauses.append({"body": [jconcept(False, dname, 0)], "head": []})
                else:
                    ht_clauses.append({"body": [jconcept(False, dname, 0)],
                                       "head": [jconcept(False, cn, 0)]})
        ht_clauses.append({"body": bod, "head": [{"k": "e", "r": rid(rec["role"]), "neg": False, "c": fil, "t": 0}]})
        # domain-obligation propagation: a node carrying this ∃r obligation is a
        # domain instance of r and of every super-role of r, even when blocking
        # stops the edge from being realised. Emit `Body → D(x)` (Horn, no branch).
        for sup in super_roles(rec["role"]):
            for d in domains.get(sup, []):
                ht_clauses.append({"body": bod, "head": [jconcept(False, d, 0)]})

    # slot disjointness: the two successors of a ≥n distinctness pair carry
    # disjoint slot concepts, so no ≤-rule merge can collapse them.
    for fi, fj in distinct_pairs:
        ht_clauses.append({"body": [jconcept(False, "__slot__%s" % fi, 0),
                                    jconcept(False, "__slot__%s" % fj, 0)],
                           "head": []})

    # ---- emit passthrough (function-free) clauses ----
    for c in passthrough:
        vm = mk_varmap()
        bod, hed = [], []
        bad = False
        for a in c["body"]:
            if a["kind"] == "concept" and a["term"].get("kind") == "var":
                bod.append(jconcept(False, a["concept"], vnum(a["term"]["name"], vm)))
            elif a["kind"] == "role" and a["source"].get("kind") == "var" and a["target"].get("kind") == "var":
                bod.append({"k": "r", "r": rid(a["role"]),
                            "s": vnum(a["source"]["name"], vm), "t": vnum(a["target"]["name"], vm)})
            else:
                bad = True
        for a in c["head"]:
            if a["kind"] == "concept" and a["term"].get("kind") == "var":
                if is_bottom(a["concept"]):
                    continue  # ⊥ disjunct -> drop (clause closes via empty head if all dropped)
                hed.append(jconcept(False, a["concept"], vnum(a["term"]["name"], vm)))
            elif a["kind"] == "role" and a["source"].get("kind") == "var" and a["target"].get("kind") == "var":
                hed.append({"k": "r", "r": rid(a["role"]),
                            "s": vnum(a["source"]["name"], vm), "t": vnum(a["target"]["name"], vm)})
            else:
                bad = True
        if bad:
            dropped += 1
            continue
        ht_clauses.append({"body": bod, "head": hed})

    # ---- emit eq clauses (≤n / functional / inverse-functional) ----
    # Function-free clauses carrying equality atoms. The eq head atom
    # `{"k":"eq",...}` is discharged by the tableau by *merging* the two nodes;
    # a head with ≥2 eq disjuncts (a ≤n with n≥1) becomes a branch point. The
    # presence of any eq head switches the tableau onto its merge-capable path.
    def jeq(va, vb):
        return {"k": "eq", "s": va, "t": vb}

    number = False
    for c in eq_clauses:
        vm = mk_varmap()
        bod, hed = [], []
        bad = False
        for a in c["body"]:
            if a["kind"] == "concept" and a["term"].get("kind") == "var":
                bod.append(jconcept(False, a["concept"], vnum(a["term"]["name"], vm)))
            elif a["kind"] == "role" and a["source"].get("kind") == "var" and a["target"].get("kind") == "var":
                bod.append({"k": "r", "r": rid(a["role"]),
                            "s": vnum(a["source"]["name"], vm), "t": vnum(a["target"]["name"], vm)})
            elif a["kind"] == "eq" and a["left"].get("kind") == "var" and a["right"].get("kind") == "var":
                bod.append(jeq(vnum(a["left"]["name"], vm), vnum(a["right"]["name"], vm)))
            else:
                bad = True
        for a in c["head"]:
            if a["kind"] == "eq" and a["left"].get("kind") == "var" and a["right"].get("kind") == "var":
                hed.append(jeq(vnum(a["left"]["name"], vm), vnum(a["right"]["name"], vm)))
            elif a["kind"] == "concept" and a["term"].get("kind") == "var":
                if is_bottom(a["concept"]):
                    continue
                hed.append(jconcept(False, a["concept"], vnum(a["term"]["name"], vm)))
            elif a["kind"] == "role" and a["source"].get("kind") == "var" and a["target"].get("kind") == "var":
                hed.append({"k": "r", "r": rid(a["role"]),
                            "s": vnum(a["source"]["name"], vm), "t": vnum(a["target"]["name"], vm)})
            else:
                bad = True
        if bad:
            dropped += 1
            continue
        if any(h.get("k") == "eq" for h in hed):
            number = True
        ht_clauses.append({"body": bod, "head": hed})

    # ---- emit RBox edge clauses (role hierarchy / domain / range) ----
    # All Horn (deterministic, no branching). domain is the backward edge clause
    # `r(x,y) → D(x)`: it only asserts D where r genuinely has a successor, so it
    # is sound; the blocked-node case is recovered by the domain-obligation
    # propagation emitted with the existentials above.
    for sub, sup in subrole_pairs:
        ht_clauses.append({"body": [{"k": "r", "r": rid(sub), "s": 0, "t": 1}],
                           "head": [{"k": "r", "r": rid(sup), "s": 0, "t": 1}]})
    # inverse roles r ≡ s⁻: materialise BOTH edge directions as clauses so the
    # existing role matching navigates inverse. r(x,y)→s(y,x) and s(x,y)→r(y,x).
    # Presence of any inverse pair switches the tableau to pairwise blocking.
    for a, b in inverse_pairs:
        ht_clauses.append({"body": [{"k": "r", "r": rid(a), "s": 0, "t": 1}],
                           "head": [{"k": "r", "r": rid(b), "s": 1, "t": 0}]})
        ht_clauses.append({"body": [{"k": "r", "r": rid(b), "s": 0, "t": 1}],
                           "head": [{"k": "r", "r": rid(a), "s": 1, "t": 0}]})
    for r, ds in domains.items():
        for d in ds:
            ht_clauses.append({"body": [{"k": "r", "r": rid(r), "s": 0, "t": 1}],
                               "head": [jconcept(False, d, 0)]})
    for r, cs in ranges.items():
        for c in cs:
            ht_clauses.append({"body": [{"k": "r", "r": rid(r), "s": 0, "t": 1}],
                               "head": [jconcept(False, c, 1)]})

    # Nominals (`{a}`) surface as `__nom__<ind>` concept names, each a singleton.
    # The tableau enforces the "exactly one instance" semantics with the o-rule
    # (merge any two nodes carrying the same nominal) plus a seeded non-blockable
    # root per nominal, so the proxy ids are emitted in `nominals` (SHOQ: sound
    # with the number merge + equality blocking already in place). The ABox facts
    # `C(a)` are already lifted by the front-end to `__nom__a(x) → C(x)` clauses.
    nom_names = sorted({n for n in con_names if short(n).startswith("__nom__")})
    nominal_ids = [con_id[n] for n in nom_names]

    # inverse + nominals = SHOI/SHOIQ: nominal/inverse interaction needs the
    # msh09 NI-rule (root chains can grow unboundedly) which is not built, so
    # fence it rather than risk a non-terminating or incomplete answer. SHOQ
    # (nominals + number, no inverse) is handled.
    if nominal_ids and inverse_pairs:
        fenced.append({"reason": "nominal+inverse(SHOI/SHOIQ)",
                       "detail": "%d nominal(s) together with inverse roles"
                       % len(nominal_ids)})
        nominal_ids = []  # fenced: do not run the nominal path

    # inverse + number restrictions = SHIQ: the merge machinery + pairwise
    # blocking interaction is not yet validated, so fence it rather than risk an
    # unsound/incomplete answer. SHQ (number, no inverse) and SHI (inverse, no
    # number) are each handled and validated separately.
    if inverse_pairs and number:
        fenced.append({"reason": "inverse+number(SHIQ)",
                       "detail": "inverse roles together with number restrictions"})

    # ---- transitivity completeness: Horrocks-Sattler universal propagation ----
    # KM_HT anywhere-subset blocking can drop transitive-role consequences (a
    # blocked node never realises its R-successors, so a ∀R.C constraint that
    # should reach the unravelled tail is lost). For a transitive role R and a
    # canonical universal U = ∀R.C (clause R(x,y) ∧ U(x) → C(y)), the rule
    #   U(x) ∧ R(x,y) → U(y)
    # is sound (any R-successor of y is, by transitivity, an R-successor of x, so
    # already has C) and restores completeness under subset blocking. Detect
    # transitive roles from the R∘R⊑R composition clauses. Gated by
    # KM_HT_NO_TRANS_ENC. No effect on ontologies without transitive roles.
    transitive_roles = set()
    if "KM_HT_NO_TRANS_ENC" not in os.environ:
        for c in ht_clauses:
            rb = [a for a in c["body"] if a.get("k") == "r"]
            rh = [a for a in c["head"] if a.get("k") == "r"]
            if len(c["body"]) == 2 and len(rb) == 2 and len(c["head"]) == 1 and len(rh) == 1:
                r1, r2 = rb
                h = rh[0]
                if (r1["r"] == r2["r"] == h["r"] and r1["t"] == r2["s"]
                        and h["s"] == r1["s"] and h["t"] == r2["t"] and r1["s"] != r2["t"]):
                    transitive_roles.add(h["r"])
        extra = []
        seen = set()
        if transitive_roles:
            for c in ht_clauses:
                rb = [a for a in c["body"] if a.get("k") == "r"]
                cb = [a for a in c["body"] if a.get("k") == "c"]
                ch = [a for a in c["head"] if a.get("k") == "c"]
                if len(c["body"]) == 2 and len(rb) == 1 and len(cb) == 1:
                    r = rb[0]
                    u = cb[0]
                    if (r["r"] in transitive_roles and not u.get("neg")
                            and u["t"] == r["s"]
                            and any(cc["t"] == r["t"] for cc in ch)):
                        key = (r["r"], u["c"])
                        if key not in seen:
                            seen.add(key)
                            extra.append({
                                "body": [{"k": "r", "r": r["r"], "s": r["s"], "t": r["t"]},
                                         {"k": "c", "neg": False, "c": u["c"], "t": r["s"]}],
                                "head": [{"k": "c", "neg": False, "c": u["c"], "t": r["t"]}]})
        ht_clauses.extend(extra)

    # a declared (named) class is always a query, even if its local name looks
    # internal (Q_minus, Q_plus, ...); only genuinely synthetic concepts
    # (definers, slots, nominals — never declared) are excluded.
    queries = [cid(n) for n in con_names
               if (n in named_set or not is_internal(n)) and not is_bottom(n)]
    # KM_HT_EMELIM: eliminate complementary-definer excluded-middle disjunctions
    # (B≡¬A) so they stop firing/branching on every node (the HT model-fold gap).
    if os.environ.get("KM_HT_EMELIM"):
        ht_clauses, n_elim = elim_complements(ht_clauses, con_names)
        if os.environ.get("KM_HT_STATS"):
            sys.stderr.write("cb_to_ht [emelim] eliminated %d complementary pairs\n" % n_elim)
    return {"concepts": con_names, "roles": rol_names, "clauses": ht_clauses,
            "queries": sorted(set(queries)), "dropped": dropped, "fenced": fenced,
            "inverse": bool(inverse_pairs), "number": number,
            "nominals": sorted(set(nominal_ids))}


def main():
    data = json.load(sys.stdin)
    out = convert(data["clauses"], data.get("rbox"))
    json.dump(out, sys.stdout)


if __name__ == "__main__":
    main()
