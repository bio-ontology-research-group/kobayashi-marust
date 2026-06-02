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

def short(name: str) -> str:
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
    if head == "ObjectHasSelf":
        return sx.HasSelf(role_cls(args[0]))
    raise ValueError(f"class: {head}")


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
    elif head in ("Declaration", "Prefix", "Import", "Annotation", "AnnotationAssertion",
                  "DisjointObjectProperties", "ObjectPropertyDomain", "ObjectPropertyRange"):
        pass  # not part of the SROIQ core we validate (domain/range could be added)
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


def ofn_to_clauses(path) -> list[dict]:
    O = parse_ontology(Path(path).read_text())
    tbox, abox, hooks = normalise(O)
    tbox = augment(tbox, abox, hooks)
    return [_clause_to_json(c) for c in tbox]


if __name__ == "__main__":
    import json
    print(json.dumps({"clauses": ofn_to_clauses(sys.argv[1])}))
