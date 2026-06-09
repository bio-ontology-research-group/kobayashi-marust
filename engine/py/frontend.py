#!/usr/bin/env python3
"""Self-contained OWL functional-syntax (`.ofn`) front-end.

Parses the OWL 2 functional syntax into moose's SROIQ AST (`moose.sroiq.syntax`)
and runs moose's *real* `normalise` + the `preprocess.augment` step to produce the
normalised DL-clauses the engine consumes — i.e. the genuine `.ofn → normalised
clauses` front-end, without depending on `pyhornedowl` (only the parser is local;
normalisation is moose's).

    ofn_to_clauses(path) -> list[dict]   # engine JSON clauses
"""
from __future__ import annotations
import os, re, sys
from pathlib import Path

# The `.ofn` front-end reuses the (separate) `moose` package for SROIQ
# normalisation.  Locate it via $MOOSE_HOME, then as a sibling of this repo.
REPO = Path(__file__).resolve().parent.parent.parent          # repo root
_candidates = ([Path(os.environ["MOOSE_HOME"])] if os.environ.get("MOOSE_HOME") else [])
_candidates += [REPO.parent / "moose", REPO / "moose"]
for _c in _candidates:
    if (_c / "moose" / "sroiq").is_dir():
        sys.path.insert(0, str(_c)); break
sys.path.insert(0, str(Path(__file__).resolve().parent))

try:
    import moose.sroiq.syntax as sx
    from moose.sroiq.normalisation import normalise
except ModuleNotFoundError as e:                              # pragma: no cover
    raise ModuleNotFoundError(
        "The .ofn front-end needs the `moose` package (SROIQ normalisation). "
        "Set MOOSE_HOME=/path/to/moose or place moose beside this repo. "
        "Note: the engine itself and all checked-in Lean proofs need no moose; "
        "only regenerating .ofn-sourced certificates does."
    ) from e
from preprocess import augment
from rust_context import _clause_to_json

# ---------------------------------------------------------------------------
# tokenizer + s-expression parser for functional syntax
# ---------------------------------------------------------------------------

# IRIs `<...>` are matched before the comment rule, so a `#` inside an IRI is
# never seen as a comment.  Comments run to end of line.
_TOK = re.compile(r'\s+|(<[^>]*>)|(\#[^\n]*)|([()])|("(?:[^"\\]|\\.)*")|([^\s()]+)')


def tokenize(text: str):
    out = []
    for m in _TOK.finditer(text):
        iri, comment, paren, lit, atom = m.groups()
        if comment is not None:
            continue
        tok = iri or paren or lit or atom
        if tok is not None and tok.strip() != "":
            out.append(tok)
    return out


class P:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.toks[self.i]
        self.i += 1
        return t

    def parse(self):
        """Return a node: a string atom, or (head, [args])."""
        t = self.next()
        if t == "(":
            raise ValueError("unexpected (")
        if self.peek() == "(":
            self.next()  # consume '('
            args = []
            while self.peek() != ")":
                args.append(self.parse())
            self.next()  # consume ')'
            return (t, args)
        return t


# ---------------------------------------------------------------------------
# IRI / name shortening
# ---------------------------------------------------------------------------

def _short_base(name: str) -> str:
    """Fragment / local-name of an IRI. NOT collision-safe on its own: two IRIs
    that share a fragment (e.g. `…/OBO_REL#part_of` and `…/obo#part_of`) collapse
    to the same string. Use `short()`, which disambiguates collisions."""
    name = name.strip()
    if name.startswith("<") and name.endswith(">"):
        name = name[1:-1]
    if "#" in name:
        return name.rsplit("#", 1)[1]
    if name.startswith(":"):
        return name[1:]
    if name.startswith("owl:"):
        return name  # keep owl:Thing / owl:Nothing for special-casing
    if "/" in name and "://" in name:
        return name.rsplit("/", 1)[1]
    if ":" in name:                # other prefixed name pfx:Local
        return name.split(":", 1)[1]
    return name


# Collision-safe IRI -> internal-name registry, reset per ontology in
# `ofn_to_clauses`. Distinct full IRIs MUST get distinct internal names: the
# engine reasons over these names, so collapsing `…/OBO_REL#part_of` and
# `…/obo#part_of` to `part_of` makes a role-hierarchy axiom on one apply to the
# other and derives unsound subsumptions (witnessed on ORE ore_ont_3978).
# Unique local names are returned unchanged, so non-colliding ontologies (and
# every existing certificate / classification output) are byte-identical.
_short_iri: dict[str, str] = {}   # full IRI -> assigned unique short name
_short_owner: dict[str, str] = {}  # short name -> full IRI that owns it


def reset_short() -> None:
    _short_iri.clear()
    _short_owner.clear()


def short(name: str) -> str:
    raw = name.strip()
    full = raw[1:-1] if raw.startswith("<") and raw.endswith(">") else raw
    cached = _short_iri.get(full)
    if cached is not None:
        return cached
    base = _short_base(name)
    if base in ("owl:Thing", "owl:Nothing"):   # specials: never disambiguate
        _short_iri[full] = base
        return base
    cand = base
    owner = _short_owner.get(cand)
    if owner is not None and owner != full:     # collision with a different IRI
        ns = full[: len(full) - len(base)].rstrip("#/:")
        tag = _short_base(ns) or "ns"
        cand = f"{base}__{tag}"
        i = 2
        while _short_owner.get(cand, full) != full:
            cand = f"{base}__{tag}{i}"
            i += 1
    _short_owner[cand] = full
    _short_iri[full] = cand
    return cand


def full_iri(internal: str) -> str:
    """Map an engine-internal name back to the *full* IRI of the class/role it
    denotes (the inverse of the per-ontology `short` registry). Classification
    output uses this so the comparison harness canonicalises km exactly like the
    other reasoners (Konclude/ELK/HermiT all emit full IRIs and the harness
    applies ore_canon.localname once). Emitting the already-shortened local name
    instead made the harness apply localname a SECOND time, truncating fragments
    that contain '/' or an embedded IRI (e.g. '…#C2/C3_facet_joint' ->
    'C3_facet_joint'; the _hasValue surrogate -> 'SWO_0000023'), which showed as
    spurious extra+missing vs gold. Names with no registered IRI (generated
    Q_*/__*, builtins) are returned unchanged."""
    return _short_owner.get(internal, internal)


def is_named_iri(internal: str) -> bool:
    """True if `internal` is the engine name of a real OWL IRI (declared/used in
    the ontology). moose's normalisation concepts (`Q_<n>`, `__*`, …) are
    generated, never IRI-backed, so this distinguishes a real class that merely
    *looks* internal (e.g. a `Q_minus` class in symbols.owl) from a genuine
    internal concept — the name-prefix heuristic alone gives false positives."""
    return internal in _short_owner


def local_name(internal: str) -> str:
    """Map an engine-internal name back to the OWL *local name* (fragment after
    the last `#`/`/`) of the IRI that owns it. `short()` disambiguates distinct
    IRIs that share a fragment (e.g. three `…/LineString`) so the engine reasons
    over them separately and soundly, but classification *output* must collapse
    them back to the bare local name — that is what every reasoner-comparison
    harness does (ore_canon.localname), so the disambiguation suffix would
    otherwise show as a spurious miss/extra against the gold signature. Names
    not in the registry (internal `Q_*`, builtins) are returned unchanged."""
    full = _short_owner.get(internal)
    if full is None:
        return internal
    return _short_base("<" + full + ">")


# ---------------------------------------------------------------------------
# class / role expression -> sx
# ---------------------------------------------------------------------------

def role_str(node) -> str:
    """A *named* role (for RBox axioms / assertions): a short string."""
    if isinstance(node, str):
        return short(node)
    raise ValueError(f"named role expected, got {node}")


def role_cls(node):
    """A role *expression* for class constructs: `str` or `InverseRole`."""
    if isinstance(node, str):
        return short(node)
    head, args = node
    if head == "ObjectInverseOf":
        return sx.InverseRole(short(args[0]))
    raise ValueError(f"role: {head}")


class OutOfFragment(Exception):
    """The ontology uses a construct outside KM's supported fragment. We fence
    the whole ontology as unsupported rather than crash or silently drop the
    constraint — silently dropping it would weaken the theory and report an
    incomplete classification as if it were complete."""


def _dt_concept(dr):
    """Abstract an OWL data range as a fresh, output-filtered concept (``__dt__``
    prefix → dropped by owl_classify.is_internal).

    The ORE 2015 datatype ontologies use no DatatypeRestriction (facets), so
    datatype satisfiability never hinges on numeric/string constraints; the only
    classification-relevant effects are data-property *domains* (Horn, handled in
    add_axiom) and the mere presence of a data successor. We therefore model each
    named datatype as a distinct opaque concept and every complex data range as a
    single opaque concept. This is a sound over-approximation: data fillers are
    fresh concepts never asserted disjoint, so abstraction can only *lose* an
    unsatisfiability (incompleteness), never invent a subsumption (unsoundness)."""
    if isinstance(dr, str):
        return sx.ConceptName("__dt__" + _short_base(dr))
    return sx.ConceptName("__dt__opaque")


def _dt_value_concept(args):
    """``DataHasValue(p v)`` ≡ ∃p.{v}: the filler must distinguish the literal
    value ``v``. Sharing one ``__dt__val`` concept across all values collapses
    e.g. ``Chinese ≡ ∃langCode."zh"`` and ``English ≡ ∃langCode."en"`` into the
    same concept, inventing the unsound subsumption Chinese ≡ English (seen on
    ore_ont_13132 / 9881). Keying by the literal keeps the _dt_concept invariant:
    distinct data values are distinct, never-disjoint concepts, so the
    abstraction can only lose an unsatisfiability, never invent a subsumption.
    The functional-syntax literal ``"zh"^^xsd:string`` tokenises to the value
    ``args[1]`` (the datatype is args[2])."""
    val = args[1] if len(args) > 1 and isinstance(args[1], str) else None
    return sx.ConceptName("__dt__val__" + val if val else "__dt__val__opaque")


def cls(node):
    if isinstance(node, str):
        s = short(node)
        if s in ("owl:Thing", "Thing"):
            return sx.Top()
        if s in ("owl:Nothing", "Nothing"):
            return sx.Bottom()
        return sx.ConceptName(s)
    head, args = node
    if head == "ObjectIntersectionOf":
        return sx.mkAnd(*(cls(a) for a in args))
    if head == "ObjectUnionOf":
        return sx.mkOr(*(cls(a) for a in args))
    if head == "ObjectComplementOf":
        return sx.Not(cls(args[0]))
    if head == "ObjectSomeValuesFrom":
        return sx.Exists(role_cls(args[0]), cls(args[1]))
    if head == "ObjectAllValuesFrom":
        return sx.Forall(role_cls(args[0]), cls(args[1]))
    if head in ("ObjectMinCardinality", "ObjectMaxCardinality", "ObjectExactCardinality"):
        n = int(args[0])
        r = role_cls(args[1])
        filler = cls(args[2]) if len(args) > 2 else sx.Top()
        if head == "ObjectMinCardinality":
            return sx.AtLeast(n, r, filler)
        if head == "ObjectMaxCardinality":
            return sx.AtMost(n, r, filler)
        return sx.mkAnd(sx.AtLeast(n, r, filler), sx.AtMost(n, r, filler))
    if head == "ObjectOneOf":
        noms = [sx.Nominal(short(a)) for a in args]
        return noms[0] if len(noms) == 1 else sx.mkOr(*noms)
    if head == "ObjectHasValue":
        # ObjectHasValue(R a) ≡ ∃R.{a}. Surfacing the nominal lets the converter
        # fence it cleanly rather than the parser raising (which read as CBERR).
        return sx.Exists(role_cls(args[0]), sx.Nominal(short(args[1])))
    if head == "ObjectHasSelf":
        return sx.HasSelf(role_cls(args[0]))
    # ---- datatype constructs: sound abstraction (see _dt_concept) ----
    if head == "DataSomeValuesFrom":
        return sx.Exists(short(args[0]), _dt_concept(args[1]))
    if head == "DataAllValuesFrom":
        return sx.Forall(short(args[0]), _dt_concept(args[1]))
    if head == "DataHasValue":
        return sx.Exists(short(args[0]), _dt_value_concept(args))
    if head in ("DataMinCardinality", "DataMaxCardinality", "DataExactCardinality"):
        n = int(args[0])
        r = short(args[1])
        filler = _dt_concept(args[2]) if len(args) > 2 else sx.ConceptName("__dt__val")
        if head == "DataMinCardinality":
            return sx.AtLeast(n, r, filler)
        if head == "DataMaxCardinality":
            return sx.AtMost(n, r, filler)
        return sx.mkAnd(sx.AtLeast(n, r, filler), sx.AtMost(n, r, filler))
    if head.startswith("Data"):     # complex data range as a top-level concept
        raise OutOfFragment(f"datatype reasoning not supported: {head}")
    raise OutOfFragment(f"unsupported class construct: {head}")


# ---------------------------------------------------------------------------
# axioms -> sx, added to Ontology
# ---------------------------------------------------------------------------

def add_axiom(O, node):
    if isinstance(node, str):
        return
    head, args = node
    # drop leading annotations
    args = [a for a in args if not (isinstance(a, tuple) and a[0] == "Annotation")]
    if head == "SubClassOf":
        O.add(sx.SubClassOf(cls(args[0]), cls(args[1])))
    elif head == "EquivalentClasses":
        cs = [cls(a) for a in args]
        for k in range(len(cs) - 1):
            O.add(sx.EquivalentClasses(cs[k], cs[k + 1]))
    elif head == "DisjointClasses":
        cs = [cls(a) for a in args]
        for k in range(len(cs)):
            for l in range(k + 1, len(cs)):
                O.add(sx.DisjointClasses(cs[k], cs[l]))
    elif head == "SubObjectPropertyOf":
        sub = args[0]
        if isinstance(sub, tuple) and sub[0] == "ObjectPropertyChain":
            O.add(sx.RoleChain(tuple(role_str(r) for r in sub[1]), role_str(args[1])))
        else:
            O.add(sx.RoleInclusion(role_str(sub), role_str(args[1])))
    elif head == "InverseObjectProperties":
        O.add(sx.InverseRoles(role_str(args[0]), role_str(args[1])))
    elif head == "TransitiveObjectProperty":
        O.add(sx.TransitiveRole(role_str(args[0])))
    elif head == "SymmetricObjectProperty":
        O.add(sx.SymmetricRole(role_str(args[0])))
    elif head == "ReflexiveObjectProperty":
        O.add(sx.ReflexiveRole(role_str(args[0])))
    elif head == "FunctionalObjectProperty":
        O.add(sx.FunctionalRole(role_str(args[0])))
    elif head == "InverseFunctionalObjectProperty":
        O.add(sx.InverseFunctionalRole(role_str(args[0])))
    elif head == "AsymmetricObjectProperty":
        O.add(sx.AsymmetricRole(role_str(args[0])))
    elif head == "IrreflexiveObjectProperty":
        O.add(sx.IrreflexiveRole(role_str(args[0])))
    elif head == "ClassAssertion":
        O.add(sx.ConceptAssertion(cls(args[0]), short(args[1])))
    elif head == "ObjectPropertyAssertion":
        O.add(sx.RoleAssertion(role_str(args[0]), short(args[1]), short(args[2])))
    elif head == "SameIndividual":
        ids = [short(a) for a in args]
        for k in range(len(ids) - 1):
            O.add(sx.SameIndividual(ids[k], ids[k + 1]))
    elif head == "DifferentIndividuals":
        ids = [short(a) for a in args]
        for k in range(len(ids)):
            for l in range(k + 1, len(ids)):
                O.add(sx.DifferentIndividuals(ids[k], ids[l]))
    elif head == "DataPropertyDomain":
        # domain(p) = C  ≡  ∃p.⊤ ⊑ C : Horn, affects class subsumption.
        O.add(sx.SubClassOf(sx.Exists(short(args[0]), sx.Top()), cls(args[1])))
    elif head in ("Declaration", "Prefix", "Import", "Annotation", "AnnotationAssertion",
                  "DisjointObjectProperties", "ObjectPropertyDomain", "ObjectPropertyRange"):
        pass  # not part of the SROIQ core we validate (domain/range could be added)
    elif head.startswith("Data") or head in ("DatatypeDefinition", "HasKey"):
        # Remaining datatype axioms (range, assertions, functional, sub/equiv data
        # property, key, datatype definitions) carry no class-subsumption effect in
        # the absence of facet restrictions, so abstracting them away is a sound
        # over-approximation (we may miss a datatype-driven unsatisfiability, i.e.
        # be incomplete, but never derive an unsound subsumption). See _dt_concept.
        pass
    # anything else: silently skipped


def parse_ontology(text: str) -> sx.Ontology:
    toks = tokenize(text)
    p = P(toks)
    O = sx.Ontology()
    # find the Ontology(...) node (skip leading Prefix(...) etc.)
    while p.peek() is not None:
        node = p.parse()
        if isinstance(node, tuple) and node[0] == "Ontology":
            for a in node[1]:
                add_axiom(O, a)
    return O


def declared_classes(text: str) -> list[str]:
    """Short names of every `Declaration(Class(...))` in the ontology, owl:Thing
    / owl:Nothing excluded. Run *after* the main parse so the collision-safe
    `short` registry is already populated and returns the same names."""
    toks = tokenize(text)
    p = P(toks)
    out = []
    while p.peek() is not None:
        node = p.parse()
        if isinstance(node, tuple) and node[0] == "Ontology":
            for a in node[1]:
                if (isinstance(a, tuple) and a[0] == "Declaration"
                        and a[1] and isinstance(a[1][0], tuple)
                        and a[1][0][0] == "Class" and a[1][0][1]):
                    s = short(a[1][0][1][0])
                    if s not in ("owl:Thing", "owl:Nothing"):
                        out.append(s)
    return out


def _concept_names_in(clauses) -> set:
    """Concept names that appear (body or head) in a list of JSON clauses."""
    names = set()
    for c in clauses:
        for side in ("body", "head"):
            for atom in c.get(side, ()):
                if atom.get("kind") == "concept":
                    names.add(atom["concept"])
    return names


def ofn_to_clauses(path) -> list[dict]:
    reset_short()   # fresh IRI->name registry per ontology (collision-safe short)
    text = Path(path).read_text()
    O = parse_ontology(text)
    tbox, abox, hooks = normalise(O)
    tbox = augment(tbox, abox, hooks)
    # moose's normalise folds role hierarchy and transitivity into the clauses
    # but not domain/range (the Rust engine has no domain/range trigger), so add
    # them as Horn clauses here — otherwise the CB path silently loses every
    # ObjectPropertyDomain/Range axiom. See preprocess.domain_range_clauses.
    from preprocess import domain_range_clauses
    tbox = list(tbox) + domain_range_clauses(ofn_rbox(path))
    jclauses = [_clause_to_json(c) for c in tbox]
    # Seed every *declared* class that appears in no clause with a tautological
    # self-clause `A(x) → A(x)`. The CB engine only classifies concepts that
    # reach its signature (named_queries), so an isolated declared class never
    # receives global axioms like `⊤ ⊑ B`. Konclude classifies all declared
    # names; matching it needs them in the signature. The self-clause is a
    # tautology (sound, pure input augmentation — calculus/Lean unchanged).
    present = _concept_names_in(jclauses)
    from moose.sroiq import dlclauses as dlc
    for name in declared_classes(text):
        if name not in present:
            present.add(name)
            atom = dlc.ConceptAtom(name, dlc.X)
            self_cl = dlc.DLClause(body=frozenset({atom}), head=frozenset({atom}))
            jclauses.append(_clause_to_json(self_cl))
    return jclauses


# ---------------------------------------------------------------------------
# RBox extraction for the hypertableau (HT) front-end
# ---------------------------------------------------------------------------
#
# moose's `normalise` folds the RBox (role hierarchy, domain, range, inverse,
# transitivity, ...) into the CB *engine's* trigger machinery, so it never
# surfaces as concept-clauses — the reverse-Skolemising `cb_to_ht` converter
# therefore cannot see it.  For the HT pipeline we re-read the RBox straight
# from the parsed functional-syntax tree (the same s-expression parser, no
# regex) and hand it to the converter as structured records.
#
# Each record is a tuple `(kind, *args)`.  Records the M1 ALC+H tableau can
# encode losslessly use named roles/classes only:
#   ("subrole", sub, sup)   r ⊑ s            -> r(x,y) → s(x,y)
#   ("range",   r, C)        range(r) = C     -> r(x,y) → C(y)
#   ("domain",  r, D)        domain(r) = D    -> ⊤ → D(x) ∨ ∀r.⊥   (blocking-safe)
# Anything that needs inverse, number, self, or non-tree edges is returned with
# a `("fenced", reason, detail)` record so the driver flags the whole ontology
# out-of-fragment rather than silently dropping a constraint.

def _plain_role(node):
    """Named role -> short string; an inverse/complex role expression -> None."""
    return short(node) if isinstance(node, str) else None


def _plain_class(node):
    """Named class -> short string; ⊤ -> "" (trivial); complex/⊥ -> None."""
    if isinstance(node, str):
        s = short(node)
        if s in ("owl:Thing", "Thing"):
            return ""          # trivial domain/range constraint, skip silently
        if s in ("owl:Nothing", "Nothing"):
            return None        # bottom domain/range: rare, fence as complex
        return s
    return None


def ofn_rbox(path) -> list:
    """Extract RBox records from a `.ofn` ontology (see module note above)."""
    toks = tokenize(Path(path).read_text())
    p = P(toks)
    nodes = []
    while p.peek() is not None:
        node = p.parse()
        if isinstance(node, tuple) and node[0] == "Ontology":
            nodes = node[1]
            break
    out = []
    for node in nodes:
        if not isinstance(node, tuple):
            continue
        head, args = node
        args = [a for a in args if not (isinstance(a, tuple) and a[0] == "Annotation")]
        if head == "SubObjectPropertyOf":
            sub, sup = args[0], args[1]
            ssup = _plain_role(sup)
            if isinstance(sub, tuple) and sub[0] == "ObjectPropertyChain":
                out.append(("fenced", "role-chain", "%s ⊑ %s" % (sub, sup)))
            elif _plain_role(sub) and ssup:
                out.append(("subrole", _plain_role(sub), ssup))
            else:
                out.append(("fenced", "inverse-role", "SubObjectPropertyOf %s ⊑ %s" % (sub, sup)))
        elif head == "ObjectPropertyDomain":
            r, d = _plain_role(args[0]), _plain_class(args[1])
            if r is None:
                out.append(("fenced", "inverse-role", "domain of %s" % (args[0],)))
            elif d is None:
                out.append(("fenced", "complex-domain", "domain(%s) = %s" % (r, args[1])))
            elif d != "":
                out.append(("domain", r, d))
        elif head == "ObjectPropertyRange":
            r, c = _plain_role(args[0]), _plain_class(args[1])
            if r is None:
                out.append(("fenced", "inverse-role", "range of %s" % (args[0],)))
            elif c is None:
                out.append(("fenced", "complex-range", "range(%s) = %s" % (r, args[1])))
            elif c != "":
                out.append(("range", r, c))
        elif head == "InverseObjectProperties":
            # r ≡ s⁻: handled in-fragment (SHI) by materialising both edge
            # directions as clauses + pairwise blocking in the tableau. Only named
            # role pairs; an inverse *expression* would be fenced elsewhere.
            a, b = _plain_role(args[0]), _plain_role(args[1])
            if a is not None and b is not None:
                out.append(("inverse", a, b))
            else:
                out.append(("fenced", "inverse-role", "InverseObjectProperties %s" % (args,)))
        elif head == "TransitiveObjectProperty":
            # Transitivity is encoded losslessly by moose's TBox normalisation as
            # `__trans__r__C` propagation concepts (not as concept-clauses we add),
            # so we do NOT fence it: subset blocking is sound for SH (transitive +
            # hierarchy, no inverse). An ontology that also has inverse/symmetric is
            # still fenced by those (SHI needs pairwise blocking, M1b). Validated
            # exact vs HermiT incl. blocking-active infinite chains and trans-through-
            # hierarchy (oracle/ontologies/trans_*.ofn).
            pass
        elif head == "SymmetricObjectProperty":
            out.append(("fenced", "symmetric-role", _plain_role(args[0]) or str(args[0])))
        elif head in ("ReflexiveObjectProperty", "IrreflexiveObjectProperty"):
            out.append(("fenced", "reflexivity", _plain_role(args[0]) or str(args[0])))
        elif head == "FunctionalObjectProperty":
            # ≤1 R.⊤. moose's normalise emits this as the DL-clause
            # `R(x,y0) ∧ R(x,y1) → ≈(y0,y1)`, which cb_to_ht turns into an eq-head
            # HT-clause the tableau discharges by merging two R-successors
            # (siblings — tree-preserving). In-fragment for SHQ, so not fenced.
            pass
        elif head == "InverseFunctionalObjectProperty":
            # ≤1 R⁻.⊤ merges two *predecessors* — an inverse-flavoured constraint
            # outside the number-only merge path. Fence until SHIQ is validated.
            out.append(("fenced", "inverse-functional", _plain_role(args[0]) or str(args[0])))
        elif head in ("AsymmetricObjectProperty", "DisjointObjectProperties"):
            out.append(("fenced", "role-constraint", head))
    return out


if __name__ == "__main__":
    import json
    print(json.dumps({"clauses": ofn_to_clauses(sys.argv[1]),
                      "rbox": ofn_rbox(sys.argv[1])}))
