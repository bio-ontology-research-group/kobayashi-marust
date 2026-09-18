#!/usr/bin/env python3
"""Cross-reasoner subsumption normaliser + FP/MISSED comparator.

Four reasoners emit four incompatible shapes. This normalises each to a sorted set
of `sub<TAB>sup` lines over NAMED classes so two runs can be diffed.

    normalise.py normalise --format <rustdl|konclude|hermit|km> FILE [--ontology SRC]
    normalise.py compare CANDIDATE.tsv ORACLE.tsv [--json]
    normalise.py gate [--only pizza,bibtex,...]

## The four input shapes (all determined empirically, see DECISIONS.md)

| reasoner | relation emitted | identifiers | equivalence |
|---|---|---|---|
| rustdl   | DIRECT (Hasse)   | full IRI    | `equiv<TAB>a<TAB>b…` line |
| Konclude | DIRECT (Hasse)   | full IRI + `abbreviatedIRI` | `EquivalentClasses` |
| HermiT   | DIRECT (Hasse)   | full IRI    | `EquivalentClasses`, one rep per group |
| KM       | TRANSITIVE CLOSURE | LOCAL NAME | mutual subsumption, + `Q_*` definers |

## Normalisation policy

R2 **Relation: transitive closure.** Three of four emit the Hasse diagram, KM emits
   the closure. The closure is the only relation all four can be brought to
   agreement on (direct -> closure is total; closure -> direct requires the input to
   be complete, which is exactly what is under test). It is also the relation
   rustdl's own `oracle_diff::aligned_closures` counts, so the committed FP=0
   reference numbers are closure counts.

R3 **owl:Thing / owl:Nothing / reflexive: dropped.** Any pair naming Thing or
   Nothing on either side is dropped, as is every reflexive `C C` pair. Konclude
   emits `X SubClassOf Thing`, HermiT does not; keeping them would make the diff a
   diff of output conventions. Thing is recognised in all three spellings that
   occur: the absolute IRI, the bare relative form `Thing` (ROBOT writes
   `<Class IRI="Thing"/>` against `xml:base`), and `abbreviatedIRI="owl:Thing"`.

R4 **Equivalent classes: expanded to mutual subsumption.** An equivalence group
   becomes the full bidirectional star, so `C ≡ D` yields both `C D` and `D C`.
   Necessary, not cosmetic: HermiT emits only ONE representative of a group in its
   SubClassOf edges (`E ⊑ C` with `D ≡ E`), so without expansion `D ⊑ C` is lost.
   Two special groups are NOT expanded but recorded as sidecar metadata:
   `EquivalentClasses(owl:Nothing, …)` members are UNSATISFIABLE and
   `EquivalentClasses(owl:Thing, …)` members are THING-EQUIVALENT. Both are
   excluded from the pair set, because reasoners disagree on whether to enumerate
   the (vacuous) pairs they participate in.

R1 **KM's Tseitin definers: whitelist, never a regex.** KM leaks internal definers
   (`Q_1`, `Q_10`, …) into `subsumptions`. A `^Q_\d+$` blacklist would silently eat
   a legitimate class named `Q_1`. Instead every KM name is checked against the set
   of classes DECLARED in the source ontology (`--ontology`), keyed by local name —
   a whitelist, the same shape as rustdl's `reportable_class_iris`. Anything not
   declared in the input cannot be a legitimate answer. This also solves KM's other
   problem: it reports LOCAL NAMES, not IRIs, so the whitelist doubles as the
   local-name -> full-IRI map needed to compare it against the other three.

## Symmetric exclusion (why normalise emits sidecar lines)

The unsat / thing-equivalent exclusion must be applied SYMMETRICALLY across both
sides of a diff -- if reasoner A proves C unsatisfiable and B does not, then B's
pairs mentioning C are an artefact of that disagreement, not false positives. A
single-file normaliser cannot know the other side's unsat set, so it emits its own
as machine-readable `#unsat` / `#thing-equiv` comment lines and `compare` takes the
union. Data lines never start with `#`, so a consumer that only wants pairs can
`grep -v '^#'`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import xml.etree.ElementTree as ET
from collections import defaultdict

OWL_THING = "http://www.w3.org/2002/07/owl#Thing"
OWL_NOTHING = "http://www.w3.org/2002/07/owl#Nothing"


def is_thing(iri: str) -> bool:
    """Recognise owl:Thing in every spelling that occurs in real output.

    `Thing` (bare) is ROBOT/HermiT writing a relative IRI against `xml:base`;
    `owl:Thing` is an unexpanded abbreviatedIRI. Missing either inflates the pair
    count by ~1 per class (rustdl measured galen FP=2748 = its class count from
    exactly this bug).
    """
    return iri in (OWL_THING, "Thing", "owl:Thing")


def is_nothing(iri: str) -> bool:
    return iri in (OWL_NOTHING, "Nothing", "owl:Nothing")


def is_special(iri: str) -> bool:
    return is_thing(iri) or is_nothing(iri)


class Normalised:
    """A reasoner's answer on one ontology, on the common basis."""

    def __init__(self, source: str = "", reasoner: str = ""):
        self.source = source
        self.reasoner = reasoner
        self.edges: set[tuple[str, str]] = set()   # as emitted (direct or closed)
        self.unsat: set[str] = set()
        self.thing_equiv: set[str] = set()

    def add_edge(self, s: str, t: str) -> None:
        """Add a subsumption, applying the R3 Thing/Nothing/reflexive policy."""
        if is_special(s) or is_special(t) or s == t:
            return
        self.edges.add((s, t))

    def add_equiv_group(self, members: list[str]) -> None:
        """Apply R4 to one equivalence group."""
        if any(is_nothing(m) for m in members):
            self.unsat.update(m for m in members if not is_nothing(m))
            return
        if any(is_thing(m) for m in members):
            self.thing_equiv.update(m for m in members if not is_thing(m))
            return
        for a in members:
            for b in members:
                self.add_edge(a, b)

    def closure(self) -> set[tuple[str, str]]:
        """R2: transitive closure, minus reflexive pairs."""
        succ: dict[str, set[str]] = defaultdict(set)
        for s, t in self.edges:
            succ[s].add(t)
        changed = True
        while changed:
            changed = False
            for s in list(succ.keys()):
                add = set()
                for t in succ[s]:
                    for u in succ.get(t, ()):
                        if u != s and u not in succ[s]:
                            add.add(u)
                if add:
                    succ[s] |= add
                    changed = True
        return {(s, t) for s, ts in succ.items() for t in ts}

    def pairs(self) -> set[tuple[str, str]]:
        """Closure with this file's OWN unsat/thing-equiv excluded (single-file view)."""
        return self.restricted(self.unsat | self.thing_equiv)

    def restricted(self, exclude: set[str]) -> set[tuple[str, str]]:
        return {
            (s, t) for (s, t) in self.closure() if s not in exclude and t not in exclude
        }

    def write(self, out) -> None:
        out.write(f"#reasoner\t{self.reasoner}\n")
        out.write(f"#source\t{self.source}\n")
        out.write("#relation\tclosure\n")
        for c in sorted(self.unsat):
            out.write(f"#unsat\t{c}\n")
        for c in sorted(self.thing_equiv):
            out.write(f"#thing-equiv\t{c}\n")
        for s, t in sorted(self.pairs()):
            out.write(f"{s}\t{t}\n")


def read_normalised(path: str) -> Normalised:
    """Read back a file written by `write`."""
    n = Normalised(source=path)
    with _open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            # A '#'-prefixed line is metadata ONLY if its first field is a known
            # sidecar key. An unresolved relative IRI is a legitimate class name
            # starting with '#', and treating those as comments silently dropped 481
            # of wine's 653 pairs -- a wrong-in-silence failure that made `compare`
            # disagree with `gate` on the same file. Fail loudly instead.
            if line.startswith("#"):
                parts = line.split("\t")
                key = parts[0]
                if key in ("#unsat", "#thing-equiv", "#reasoner", "#source", "#relation"):
                    if len(parts) >= 2:
                        if key == "#unsat":
                            n.unsat.add(parts[1])
                        elif key == "#thing-equiv":
                            n.thing_equiv.add(parts[1])
                        elif key == "#reasoner":
                            n.reasoner = parts[1]
                    continue
                if len(parts) == 2:
                    raise SystemExit(
                        f"{path}: line starts with '#' but is not a known sidecar key, "
                        f"so it is an unresolved relative IRI being lost as a comment: "
                        f"{line!r}"
                    )
                continue
            parts = line.split("\t")
            if len(parts) == 2:
                n.edges.add((parts[0], parts[1]))
    return n


# ── parsers ─────────────────────────────────────────────────────────────────


def _local(iri: str) -> str:
    """Local name of an IRI: the part after the last '#' or '/'."""
    for sep in ("#", "/"):
        if sep in iri:
            iri = iri.rsplit(sep, 1)[1]
    return iri


def parse_owx(path: str, reasoner: str = "konclude") -> Normalised:
    """Konclude (and any) OWL/XML classification output.

    Uses a real XML parser and EXPANDS `abbreviatedIRI` against the document's
    `<Prefix>` declarations. This is not pedantry: wine's Konclude output carries
    736 `food:*` abbreviated IRIs alongside full `food#` IRIs for the same classes,
    so a regex that took the attribute raw would split each class in two and both
    the closure and the diff would be wrong.
    """
    n = Normalised(source=path, reasoner=reasoner)
    # Read through _open so a .gz output parses too. ElementTree.parse() takes a
    # path and would open it itself, bypassing the gzip handling every other parser
    # in this file goes through -- which made compressed Konclude output unreadable
    # while the line-based formats worked, so the transparency was only ever verified
    # on those.
    with _open(path) as _fh:
        tree = ET.parse(_fh)
    root = tree.getroot()

    def tag(e) -> str:
        return e.tag.split("}", 1)[1] if "}" in e.tag else e.tag

    prefixes: dict[str, str] = {}
    for e in root.iter():
        if tag(e) == "Prefix":
            prefixes[e.get("name", "")] = e.get("IRI", "")

    # Base for resolving fragment-only IRIs. Konclude writes the ontology's own
    # classes as RELATIVE references (`<Class IRI="#AlsatianWine"/>`, 248 of them in
    # wine): resolving them is REQUIRED for cross-reasoner identity, because HermiT
    # and rustdl both emit the absolute `…/wine#AlsatianWine` for the same class.
    # Leaving them bare made 481 of wine's 653 pairs unmatchable (they also collided
    # with this format's `#` comment sigil). Prefer ontologyIRI over xml:base to
    # match horned-owl, which is what produced the committed reference counts.
    base = root.get("ontologyIRI") or root.get(
        "{http://www.w3.org/XML/1998/namespace}base", ""
    )
    base = base.split("#", 1)[0]

    def resolve(iri: str) -> str:
        """RFC 3986 fragment resolution, applied ONLY to fragment-only references.

        Deliberately narrow: anything not starting with '#' is returned untouched, so
        the bare relative `Thing`/`Nothing` that ROBOT emits (when its output has no
        ontologyIRI) still reaches is_thing/is_nothing and stays excluded.
        """
        if iri.startswith("#") and base:
            return base + iri
        return iri

    def iri_of(e):
        """Full IRI of a <Class> element, or None if it is not a named class."""
        if tag(e) != "Class":
            return None
        if (full := e.get("IRI")) is not None:
            return resolve(full)
        if (abbr := e.get("abbreviatedIRI")) is not None:
            if ":" in abbr:
                pfx, local = abbr.split(":", 1)
                if pfx in prefixes:
                    return prefixes[pfx] + local
            return abbr
        return None

    for e in root.iter():
        t = tag(e)
        if t == "SubClassOf":
            kids = list(e)
            # atomic-only: both operands must be named classes
            if len(kids) == 2:
                a, b = iri_of(kids[0]), iri_of(kids[1])
                if a is not None and b is not None:
                    n.add_edge(a, b)
        elif t == "EquivalentClasses":
            members = [i for i in (iri_of(k) for k in e) if i is not None]
            if len(members) >= 2:
                n.add_equiv_group(members)
    return n


import gzip as _gzip


def _open(path: str):
    """Open a captured reasoner output, transparently handling gzip.

    Reasoner output compresses ~36x (OWL functional syntax; a 563 MB ontology's
    taxonomy goes to under 15 MB), and a full 1,920 x 7-arm sweep emits ~35 GB raw
    per repeat. Storing it compressed is the difference between ~35 GB and ~1 GB on a
    shared volume.

    Compression happens AFTER an arm finishes, never by piping the reasoner through
    gzip: a pipeline returns the LAST command's status, which is exactly how 22 KM
    failures were once recorded as successes.
    """
    if path.endswith(".gz"):
        return _gzip.open(path, "rt", encoding="utf-8", errors="replace")
    return open(path, encoding="utf-8", errors="replace")


def parse_hermit(path: str) -> Normalised:
    """HermiT `-c` taxonomy: `SubClassOf( <a> <b> )` / `EquivalentClasses( <a> <b> )`."""
    n = Normalised(source=path, reasoner="hermit")
    with _open(path) as fh:
        for line in fh:
            line = line.strip()
            if m := re.match(r"SubClassOf\(\s*<([^>]*)>\s*<([^>]*)>\s*\)", line):
                n.add_edge(m.group(1), m.group(2))
            elif m := re.match(r"EquivalentClasses\(\s*(.*?)\s*\)\s*$", line):
                members = re.findall(r"<([^>]*)>", m.group(1))
                if len(members) >= 2:
                    n.add_equiv_group(members)
    return n


def parse_rustdl(path: str) -> Normalised:
    """rustdl `classify` stdout: `direct<TAB>sub<TAB>sup`, `equiv<TAB>a<TAB>b…`,
    `unsat<TAB>iri`, plus `#`-prefixed banner lines."""
    n = Normalised(source=path, reasoner="rustdl")
    with _open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            if line.startswith("#"):
                continue
            parts = line.split("\t")
            if parts[0] == "direct" and len(parts) == 3:
                n.add_edge(parts[1], parts[2])
            elif parts[0] == "equiv" and len(parts) >= 3:
                n.add_equiv_group(parts[1:])
            elif parts[0] == "unsat" and len(parts) == 2:
                n.unsat.add(parts[1])
    return n


def prefix_map(ontology: str) -> dict[str, str]:
    """prefix -> namespace for every `Prefix(p:=<ns>)` in an .ofn source.

    The default prefix is the empty key, so `:Foo` resolves like any other.
    Shared by `declared_classes` and KM's prefixed-name resolver so the two cannot
    drift; KM >= v1.3.0 reports `pizza:American`, which needs this to become an IRI.
    """
    txt = _open(ontology).read()
    out: dict[str, str] = {}
    for m in re.finditer(r"Prefix\(\s*([A-Za-z0-9_.-]*):=<([^>]*)>\s*\)", txt):
        out[m.group(1)] = m.group(2)
    return out


def declared_classes(ontology: str) -> dict[str, str]:
    """local name -> full IRI for every class DECLARED in an .ofn source ontology.

    This is the R1 whitelist. Built from the source rather than from any reasoner's
    output, so no reasoner's internal synthetics can enter it.
    """
    txt = _open(ontology).read()
    prefixes = prefix_map(ontology)

    out: dict[str, str] = {}
    collisions: set[str] = set()
    for m in re.finditer(r"Declaration\(\s*Class\(\s*([^)\s]+)\s*\)\s*\)", txt):
        tok = m.group(1)
        if tok.startswith("<") and tok.endswith(">"):
            iri = tok[1:-1]
        elif ":" in tok:
            pfx, local = tok.split(":", 1)
            if pfx not in prefixes:
                continue
            iri = prefixes[pfx] + local
        else:
            continue
        if is_special(iri):
            continue
        loc = _local(iri)
        if loc in out and out[loc] != iri:
            collisions.add(loc)
        out[loc] = iri
    if collisions:
        print(
            f"WARNING: {len(collisions)} local-name collisions in {ontology} "
            f"(e.g. {sorted(collisions)[:3]}); KM output is keyed by local name and "
            "is AMBIGUOUS for these classes",
            file=sys.stderr,
        )
    return out


def parse_km(path: str, ontology: str | None) -> Normalised:
    """KM JSON, in either release format.

    * <= v0.2.3: `{"subsumptions": {"Article": ["Entry", "Q_1", …]}, …}` — a dict
      keyed by BARE LOCAL NAME.
    * >= v0.2.4: `{"subsumptions": [["http://…#Article", "http://…#Entry"], …]}` — a
      list of pairs carrying FULL IRIs.

    Both are handled. Passing the newer format to a parser expecting only the older
    one raises `AttributeError` on `.items()` — it fails loudly rather than
    silently reporting an empty closure, which matters because an empty closure
    would read as "KM missed everything" in a comparison.

    KM emits the TRANSITIVE CLOSURE keyed by LOCAL NAME, mixed with internal Tseitin
    definers. Requires `--ontology` to supply the R1 whitelist / name->IRI map.
    """
    n = Normalised(source=path, reasoner="km")
    data = json.load(_open(path))
    if ontology is None:
        raise SystemExit(
            "--format km requires --ontology SRC.ofn: KM reports bare local names and "
            "leaks Tseitin definers, so it can only be normalised against the set of "
            "classes actually declared in the source ontology (see R1)."
        )
    name_to_iri = declared_classes(ontology)
    _prefixes = prefix_map(ontology)
    _declared_iris = set(name_to_iri.values())

    def expand_prefixed(tok: str) -> str | None:
        """`pizza:American` -> full IRI, but ONLY if the result is a declared class.

        KM >= v1.3.0 emits ABBREVIATED names -- a third output shape after the
        v0.2.3 local-name dict and the v0.2.4 full-IRI pair list. Unhandled, every
        entry failed `lookup`, was counted as an internal symbol and dropped, and KM
        normalised to an EMPTY closure: measured on pizza, 0 rows where KM really
        reports 479. In a comparison that reads as "KM missed everything" rather
        than as a parser gap, which is the exact failure the format-dispatch comment
        above was written to prevent.

        Resolution goes through the prefix map and is then CHECKED against the
        declared-class whitelist, rather than falling back to matching on local name
        -- two namespaces in one ontology may share a local name, and a local-name
        fallback would silently pick one.
        """
        if "://" in tok or tok.startswith("<") or ":" not in tok:
            return None
        pfx, local = tok.split(":", 1)
        base = _prefixes.get(pfx)
        if base is None:
            return None
        iri = base + local
        return iri if iri in _declared_iris else None


    def lookup(name: str) -> str | None:
        """KM output name -> source IRI, or None if it is an internal symbol.

        KM ESCAPES source classes whose local name looks generated, prefixing
        `km_src_` (`frontend/iri.rs`: `reserved_internal_prefix` = `Thing`/`Nothing`
        or a `Q_` / `__` / `_aux` / `aux_` / `def_` prefix). So a legitimate class
        named `Q_1` is emitted as `km_src_Q_1` while KM's own definers are the
        UNescaped `Q_*`. Without un-escaping, real answers are dropped: measured on a
        probe ontology declaring `:Q_1`, 2 of 3 subsumptions were lost. Direct lookup
        is tried first so a class literally named `km_src_Q_1` still resolves to
        itself.
        """
        if (iri := name_to_iri.get(name)) is not None:
            return iri
        if name.startswith("km_src_"):
            return name_to_iri.get(name[len("km_src_"):])
        return None

    dropped: set[str] = set()
    raw = data.get("subsumptions") or {}
    if isinstance(raw, list):
        # KM >= v0.2.4 emits a LIST of [sub, sup] pairs carrying FULL IRIs, where
        # earlier releases emitted a DICT keyed by BARE LOCAL NAME. Both are
        # accepted so this parser is not silently version-locked; the older format
        # is what the 2026-07-19 head-to-head was computed against.
        #
        # Full IRIs need no name->IRI lookup, but they still go through `lookup`
        # first so an ontology that genuinely declares a `km_src_`-prefixed local
        # name keeps working; unresolvable entries fall back to the IRI as-is only
        # when it really is an absolute IRI, so internal definers are still dropped.
        pairs = []
        for entry in raw:
            if isinstance(entry, (list, tuple)) and len(entry) >= 2:
                pairs.append((str(entry[0]), str(entry[1])))
            elif isinstance(entry, dict) and "sub" in entry and "sup" in entry:
                pairs.append((str(entry["sub"]), str(entry["sup"])))
        for sub, sup in pairs:
            s_iri = lookup(sub) or expand_prefixed(sub) or (sub if "://" in sub else None)
            t_iri = lookup(sup) or expand_prefixed(sup) or (sup if "://" in sup else None)
            if s_iri is None:
                dropped.add(sub)
                continue
            if t_iri is None:
                dropped.add(sup)
                continue
            n.add_edge(s_iri, t_iri)
        if dropped:
            # NOT `n.notes.append` -- Normalised has no `notes` attribute and this
            # raised AttributeError. The path was unreachable while KM's list format
            # carried FULL IRIs (every symbol resolved, or fell through to the
            # absolute-IRI fallback); v1.3.0's abbreviated names made it live. Same
            # stderr note the dict branch emits, so the two cannot diverge.
            print(
                f"note: dropped {len(dropped)} KM names not declared in the source "
                f"ontology (Tseitin definers etc., e.g. {sorted(dropped)[:5]})",
                file=sys.stderr,
            )
        return n
    for sub, sups in raw.items():
        s_iri = lookup(sub) or expand_prefixed(sub)
        if s_iri is None:
            dropped.add(sub)
            continue
        for sup in sups:
            t_iri = lookup(sup) or expand_prefixed(sup)
            if t_iri is None:
                dropped.add(sup)
                continue
            n.add_edge(s_iri, t_iri)
    if dropped:
        print(
            f"note: dropped {len(dropped)} KM names not declared in the source "
            f"ontology (Tseitin definers etc., e.g. {sorted(dropped)[:5]})",
            file=sys.stderr,
        )
    return n


def normalise_file(fmt: str, path: str, ontology: str | None) -> Normalised:
    if fmt == "konclude":
        return parse_owx(path, "konclude")
    if fmt == "owx":
        return parse_owx(path, "owx")
    if fmt == "hermit":
        return parse_hermit(path)
    if fmt == "rustdl":
        return parse_rustdl(path)
    if fmt == "km":
        return parse_km(path, ontology)
    raise SystemExit(f"unknown format: {fmt}")


# ── compare ─────────────────────────────────────────────────────────────────


def compare(cand_path: str, oracle_path: str) -> dict:
    """FP/MISSED between two normalised files.

    FP     = candidate asserts, oracle lacks  (SOUNDNESS -- must be 0)
    MISSED = oracle has, candidate lacks      (COMPLETENESS)

    Exclusion is SYMMETRIC: the union of both sides' unsat and thing-equivalent
    classes is removed from both closures first, so a disagreement about
    satisfiability is reported as such instead of masquerading as thousands of FPs.
    """
    a = read_normalised(cand_path)
    b = read_normalised(oracle_path)
    exclude = a.unsat | b.unsat | a.thing_equiv | b.thing_equiv
    ac = a.restricted(exclude)
    bc = b.restricted(exclude)
    fp = ac - bc
    missed = bc - ac
    return {
        "candidate": cand_path,
        "candidate_reasoner": a.reasoner,
        "oracle": oracle_path,
        "oracle_reasoner": b.reasoner,
        "candidate_closure": len(ac),
        "oracle_closure": len(bc),
        "excluded_classes": len(exclude),
        "unsat_disagreement": len(a.unsat ^ b.unsat),
        "FP": len(fp),
        "MISSED": len(missed),
        "fp_sample": [list(p) for p in sorted(fp)[:10]],
        "missed_sample": [list(p) for p in sorted(missed)[:10]],
    }


# ── gate ────────────────────────────────────────────────────────────────────

RUSTDL = "/data/dumontier/rustdl"

# rustdl's committed FP=0 oracle closure counts (CLAUDE.md, 2026-07-29). These are
# known-correct reference values: normalised Konclude output MUST reproduce them.
GATE = {
    "galen": (27997, "ontologies/external/galen-classified.owx"),
    "notgalen": (32739, "ontologies/external/notgalen-classified.owx"),
    "sio": (8904, "ontologies/real/konclude-input/sio-classified.owx"),
    "ore-10908": (6001, "ontologies/external/ore-10908-sroiq-classified.owx"),
    "wine": (653, "ontologies/real/konclude-input/wine-classified.owx"),
    "pizza": (499, "ontologies/real/konclude-input/pizza-classified.owx"),
    "alehif": (247, "ontologies/external/alehif-test-classified.owx"),
    "ro": (158, "ontologies/real/konclude-input/ro-classified.owx"),
    "ore-15672": (142, "ontologies/external/ore-15672-shoin-classified.owx"),
    "sulo": (51, "ontologies/real/konclude-input/sulo-classified.owx"),
    "bibtex": (16, "ontologies/real/konclude-input/bibtex-classified.owx"),
}


def run_gate(only: list[str] | None) -> int:
    names = [n for n in GATE if only is None or n in only]
    print(f"{'fixture':<12} {'expected':>9} {'actual':>9}  verdict")
    print("-" * 46)
    fails = absent = 0
    for name in names:
        expected, rel = GATE[name]
        path = os.path.join(RUSTDL, rel)
        if not os.path.exists(path):
            print(f"{name:<12} {expected:>9} {'-':>9}  ABSENT ({rel})")
            absent += 1
            continue
        actual = len(parse_owx(path).pairs())
        ok = actual == expected
        print(f"{name:<12} {expected:>9} {actual:>9}  {'PASS' if ok else 'FAIL'}")
        if not ok:
            fails += 1
    print("-" * 46)
    verified = len(names) - absent - fails
    print(f"verified={verified} failed={fails} absent={absent}")
    if fails:
        print(
            "\nGATE FAILED: the normaliser does not reproduce rustdl's committed "
            "closure counts. Do NOT adjust the expected numbers -- they are the "
            "known-correct reference. Every downstream FP/MISSED figure would be "
            "garbage until this passes."
        )
    return 1 if fails else 0


def run_selftest() -> int:
    """Invariants the count-based gate is BLIND to, plus the two bugs it missed.

    Closure SIZE is invariant under relabelling, so `gate` passes even if every IRI
    is wrong (measured: dropping abbreviatedIRI expansion left all 11 counts exact
    while corrupting 344 of wine's pair-halves). These checks pin IDENTITY.
    """
    import tempfile

    fails: list[str] = []

    def check(name: str, got, want) -> None:
        ok = got == want
        print(f"  {'PASS' if ok else 'FAIL'}  {name}")
        if not ok:
            print(f"        got  {got}\n        want {want}")
            fails.append(name)

    d = tempfile.mkdtemp(prefix="normalise-selftest-")

    def w(fn: str, body: str) -> str:
        p = os.path.join(d, fn)
        with open(p, "w", encoding="utf-8") as fh:
            fh.write(body)
        return p

    A, B, C = "http://e#A", "http://e#B", "http://e#C"

    # R2 direct -> closure, R3 Thing/reflexive drop, R4 equiv expansion.
    owx = w("t.owx", """<?xml version="1.0"?>
<Ontology xmlns="http://www.w3.org/2002/07/owl#" xml:base="http://e" ontologyIRI="http://e">
 <Prefix name="owl" IRI="http://www.w3.org/2002/07/owl#"/>
 <Prefix name="p" IRI="http://e#"/>
 <SubClassOf><Class IRI="http://e#C"/><Class IRI="http://e#B"/></SubClassOf>
 <SubClassOf><Class IRI="http://e#B"/><Class IRI="http://e#A"/></SubClassOf>
 <SubClassOf><Class IRI="http://e#A"/><Class abbreviatedIRI="owl:Thing"/></SubClassOf>
 <SubClassOf><Class IRI="http://e#A"/><Class IRI="Thing"/></SubClassOf>
 <SubClassOf><Class IRI="http://e#A"/><Class IRI="http://e#A"/></SubClassOf>
 <EquivalentClasses><Class IRI="#D"/><Class abbreviatedIRI="p:E"/></EquivalentClasses>
 <SubClassOf><Class IRI="#D"/><Class IRI="http://e#C"/></SubClassOf>
 <EquivalentClasses><Class abbreviatedIRI="owl:Nothing"/><Class IRI="http://e#U"/></EquivalentClasses>
 <EquivalentClasses><Class abbreviatedIRI="owl:Thing"/><Class IRI="http://e#T"/></EquivalentClasses>
</Ontology>
""")
    n = parse_owx(owx)
    D, E = "http://e#D", "http://e#E"
    # R2: C->A present though only C->B, B->A were asserted.
    check("R2 direct input is transitively closed", (C, A) in n.pairs(), True)
    # R3: no Thing/Nothing pair in any spelling; no reflexive pair.
    check("R3 Thing/Nothing/reflexive dropped",
          any(is_special(s) or is_special(t) or s == t for s, t in n.pairs()), False)
    # R4: equiv expands both ways AND propagates through the group (E->C via D).
    check("R4 equiv group expands bidirectionally", {(D, E), (E, D)} <= n.pairs(), True)
    check("R4 equiv member inherits group's supers", (E, C) in n.pairs(), True)
    check("R4 unsat group recorded, not expanded", n.unsat, {"http://e#U"})
    check("R4 thing-equiv group recorded", n.thing_equiv, {"http://e#T"})
    # abbreviatedIRI expansion + relative-IRI resolution -> absolute IRIs only.
    check("abbreviatedIRI p:E expanded to full IRI", E in {s for s, _ in n.pairs()}, True)
    check("relative #D resolved against base", D in {s for s, _ in n.pairs()}, True)
    check("no unexpanded prefixed/relative IRI survives",
          [x for pr in n.pairs() for x in pr if x.startswith("#") or "://" not in x], [])

    # Serialization round-trip must not lose a pair (the wine `#`-comment collision).
    tsv = os.path.join(d, "t.tsv")
    with open(tsv, "w", encoding="utf-8") as fh:
        n.write(fh)
    check("round-trip preserves every pair", read_normalised(tsv).pairs(), n.pairs())

    # A '#'-leading data line must FAIL LOUDLY rather than be eaten as a comment.
    bad = w("bad.tsv", "#reasoner\tx\n#Foo\t#Bar\n")
    try:
        read_normalised(bad)
        check("unresolved relative IRI in tsv is rejected", "no error", "SystemExit")
    except SystemExit:
        check("unresolved relative IRI in tsv is rejected", True, True)

    # R1: KM whitelist keeps a legitimate Q_1 (escaped km_src_Q_1) and drops definers.
    ofn = w("q.ofn", "Prefix(:=<http://e#>)\nOntology(<http://e>\n"
                     "Declaration(Class(:Q_1))\nDeclaration(Class(:Mid))\n)\n")
    km = w("q.json", json.dumps({"subsumptions": {
        "km_src_Q_1": ["Mid", "Q_0"],   # real class (escaped) + definer
        "Q_0": ["Mid"],                  # pure definer subject
    }}))
    kmn = parse_km(km, ofn)
    check("R1 legitimate Q_1 survives via km_src_ un-escape",
          kmn.pairs(), {("http://e#Q_1", "http://e#Mid")})
    check("R1 Tseitin definer Q_0 dropped",
          any("Q_0" in x for pr in kmn.pairs() for x in pr), False)

    # KM >= v1.3.0 emits ABBREVIATED names in the pair-list form (`pizza:American`),
    # a third shape after the v0.2.3 local-name dict and the v0.2.4 full-IRI list.
    # Unhandled it resolves to NOTHING and KM normalises to an empty closure, which
    # reads as "KM missed everything" rather than as a parser gap: measured on pizza,
    # 0 rows against the 479 KM really reports. Covers the default (empty) prefix too.
    ofn2 = w("pfx.ofn", "Prefix(:=<http://e#>)\nPrefix(p:=<http://p#>)\n"
                        "Ontology(<http://e>\nDeclaration(Class(:A))\n"
                        "Declaration(Class(p:B))\n)\n")
    km2 = w("pfx.json", json.dumps({"subsumptions": [[":A", "p:B"]]}))
    check("KM v1.3.0 prefixed names resolve to declared IRIs",
          parse_km(km2, ofn2).pairs(), {("http://e#A", "http://p#B")})

    # A prefixed name whose expansion is NOT a declared class must still be dropped --
    # the resolver is whitelist-checked, not a local-name fallback, because two
    # namespaces in one ontology can share a local name.
    km3 = w("pfx2.json", json.dumps({"subsumptions": [[":A", "p:Undeclared"]]}))
    check("KM prefixed name outside the whitelist is dropped",
          parse_km(km3, ofn2).pairs(), set())

    print("-" * 46)
    print(f"selftest: {'FAILED ' + str(len(fails)) if fails else 'all PASS'}")
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("normalise", help="one reasoner's output -> sorted sub<TAB>sup")
    p.add_argument("--format", required=True,
                   choices=["rustdl", "konclude", "hermit", "km", "owx"])
    p.add_argument("file")
    p.add_argument("--ontology", help="source .ofn (REQUIRED for --format km)")
    p.add_argument("-o", "--out", help="output path (default stdout)")

    p = sub.add_parser("compare", help="FP/MISSED between two normalised files")
    p.add_argument("candidate")
    p.add_argument("oracle")
    p.add_argument("--json", action="store_true")

    p = sub.add_parser("gate", help="reproduce rustdl's committed closure counts")
    p.add_argument("--only", help="comma-separated fixture subset")

    sub.add_parser("selftest", help="identity invariants the count gate cannot see")

    a = ap.parse_args()

    if a.cmd == "normalise":
        n = normalise_file(a.format, a.file, a.ontology)
        if a.out:
            with open(a.out, "w", encoding="utf-8") as fh:
                n.write(fh)
        else:
            n.write(sys.stdout)
        return 0

    if a.cmd == "compare":
        res = compare(a.candidate, a.oracle)
        if a.json:
            print(json.dumps(res, indent=1))
        else:
            for k in ("candidate_reasoner", "oracle_reasoner", "candidate_closure",
                      "oracle_closure", "excluded_classes", "unsat_disagreement",
                      "FP", "MISSED"):
                print(f"{k:<22} {res[k]}")
            for label in ("fp", "missed"):
                for pair in res[f"{label}_sample"]:
                    print(f"  {label.upper():<6} {pair[0]}\t{pair[1]}")
        return 1 if res["FP"] else 0

    if a.cmd == "selftest":
        return run_selftest()

    return run_gate(a.only.split(",") if a.only else None)


if __name__ == "__main__":
    sys.exit(main())
