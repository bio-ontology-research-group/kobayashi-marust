#!/usr/bin/env python3
"""Map KM source-token result names to full IRIs without changing entailments.

The frontend's IriRegistry removes angle brackets but preserves prefixed tokens.
This benchmark adapter resolves those tokens from the exact source document.
OWL functional syntax defines expansion as prefix IRI + local part:
https://www.w3.org/TR/owl-syntax/#IRIs
"""
import gzip
import re
from pathlib import Path

STANDARD_PREFIXES = {
    'owl:': 'http://www.w3.org/2002/07/owl#',
    'rdf:': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
    'rdfs:': 'http://www.w3.org/2000/01/rdf-schema#',
    'xsd:': 'http://www.w3.org/2001/XMLSchema#',
    'xml:': 'http://www.w3.org/XML/1998/namespace',
}
TOP = STANDARD_PREFIXES['owl:'] + 'Thing'
BOTTOM = STANDARD_PREFIXES['owl:'] + 'Nothing'
ABSOLUTE = re.compile(r'^[A-Za-z][A-Za-z0-9+.-]*:')


def tokens(source):
    """Small lexical scanner; literals/comments cannot introduce fake prefixes."""
    i, n = 0, len(source)
    while i < n:
        c = source[i]
        if c.isspace():
            i += 1
        elif c == '#':
            end = source.find('\n', i)
            i = n if end < 0 else end + 1
        elif c in '()=':
            yield c
            i += 1
        elif c == '<':
            end = source.find('>', i + 1)
            if end < 0:
                raise ValueError('unterminated source IRI')
            yield source[i:end + 1]
            i = end + 1
        elif c == '"':
            i += 1
            while i < n:
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError('unterminated source literal')
            # No literal text can be a class name in a classification response.
        else:
            start = i
            while i < n and not source[i].isspace() and source[i] not in '()=<>"':
                i += 1
            if i == start:
                raise ValueError('unexpected source delimiter')
            yield source[start:i]


class SourceNames:
    """Unambiguous mapping from KM's raw output spelling to a source full IRI.

    Standard vocabulary prefixes are supplied for legacy sources that omit their
    declarations. Explicit conflicting redeclarations are rejected. No arbitrary
    undeclared prefixes or local-name heuristics are accepted.
    """
    def __init__(self, source):
        self.prefixes = dict(STANDARD_PREFIXES)
        self.names = {}
        raw_names = set()
        stream = iter(tokens(source))
        in_ontology = False
        for token in stream:
            if not in_ontology and token == 'Prefix':
                try:
                    opening, prefix, equals, iri, closing = [next(stream) for _ in range(5)]
                except StopIteration:
                    raise ValueError('incomplete Prefix declaration')
                if opening != '(' or equals != '=' or closing != ')' or not prefix.endswith(':') or not iri.startswith('<'):
                    raise ValueError('malformed Prefix declaration')
                full = iri[1:-1]
                if not ABSOLUTE.match(full):
                    raise ValueError('relative prefix IRI is unsupported')
                if prefix in self.prefixes and self.prefixes[prefix] != full:
                    raise ValueError('conflicting Prefix declaration: ' + prefix)
                self.prefixes[prefix] = full
            elif token == 'Ontology':
                in_ontology = True
            elif in_ontology:
                if token.startswith('<'):
                    full = token[1:-1]
                    if not ABSOLUTE.match(full):
                        raise ValueError('relative source IRI is unsupported')
                    self._put(full, full)
                elif ':' in token and not token.startswith(('^^', '@')):
                    raw_names.add(token)
        for raw in raw_names:
            prefix, local = raw.split(':', 1)
            prefix += ':'
            if prefix not in self.prefixes:
                raise ValueError('undeclared source prefix: ' + prefix)
            self._put(raw, self.prefixes[prefix] + local)
        # KM sometimes emits builtins even if not explicitly present in source.
        for raw, full in [('owl:Thing', TOP), ('owl:Nothing', BOTTOM), (TOP, TOP), (BOTTOM, BOTTOM)]:
            self._put(raw, full)
        self.expanded = set(self.names.values())

    def _put(self, raw, full):
        if raw in self.names and self.names[raw] != full:
            raise ValueError('ambiguous KM raw spelling for source IRIs: ' + raw)
        self.names[raw] = full

    def expand(self, raw):
        if raw.startswith('<') and raw.endswith('>'):
            full = raw[1:-1]
            if ABSOLUTE.match(full):
                return full
        if raw in self.names:
            return self.names[raw]
        # A different worker may already have expanded the same source token.
        if raw in self.expanded:
            return raw
        raise ValueError('output name absent from source mapping: ' + raw)


def canonical(result, source):
    """Shared result -> canonical text adapter; expands before builtin filtering."""
    if result['dropped']:
        raise ValueError('dropped axioms')
    if not result['consistent']:
        return 'C\tfalse\n'
    names = source if isinstance(source, SourceNames) else SourceNames(source)
    unsat = {names.expand(c) for c in result['unsatisfiable']} - {BOTTOM}
    if TOP in unsat:
        raise ValueError('consistent response marks owl:Thing unsatisfiable')
    rows = {'C\ttrue'} | {'U\t' + c for c in unsat}
    pairs = result['subsumptions']
    if isinstance(pairs, dict):
        pairs = ((a, b) for a, bs in pairs.items() for b in bs)
    for a, b in pairs:
        a, b = names.expand(a), names.expand(b)
        if a != b and a not in unsat and a not in (TOP, BOTTOM) and b not in (TOP, BOTTOM):
            rows.add('S\t' + a + '\t' + b)
    return '\n'.join(sorted(rows)) + '\n'


def canonical_signature(lines, source):
    """Transform retained raw C/U/S evidence, preserving original files."""
    names = source if isinstance(source, SourceNames) else SourceNames(source)
    result = dict(dropped=[], consistent=None, unsatisfiable=[], subsumptions=[])
    for line in lines:
        parts = line.rstrip('\n').split('\t')
        if parts[0] == 'C' and len(parts) == 2 and parts[1] in ('true', 'false') and result['consistent'] is None:
            result['consistent'] = parts[1] == 'true'
        elif parts[0] == 'U' and len(parts) == 2:
            result['unsatisfiable'].append(parts[1])
        elif parts[0] == 'S' and len(parts) == 3:
            result['subsumptions'].append(parts[1:])
        else:
            raise ValueError('malformed canonical signature')
    if result['consistent'] is None:
        raise ValueError('missing consistency status')
    if not result['consistent'] and (result['unsatisfiable'] or result['subsumptions']):
        raise ValueError('inconsistent signature contains taxonomy rows')
    return canonical(result, names)


def read_source(path):
    path = Path(path)
    return gzip.open(path, 'rt', encoding='utf-8').read() if path.suffix == '.gz' else path.read_text()


def audit_controls(root, output):
    """Reaudit small analytic controls without changing any original evidence."""
    import hashlib
    import json
    import os
    from datetime import datetime, timezone
    digest = lambda data: hashlib.sha256(data).hexdigest()
    root, output = Path(root).resolve(), Path(output).resolve()
    controls_path = root / 'inputs/controls.json'
    controls = json.loads(controls_path.read_text())
    output.mkdir(parents=True, exist_ok=False)
    report = dict(root=str(root), output=str(output), helper_sha256=digest(Path(__file__).read_bytes()),
        controls_sha256=digest(controls_path.read_bytes()), job=os.environ.get('SLURM_JOB_ID'),
        generated_utc=datetime.now(timezone.utc).isoformat(), cases={})
    for case in controls:
        states = (root / 'inputs' / case / 'pilot-states.txt').read_text().splitlines()
        rows = []
        report['cases'][case] = rows
        for arm in ('session', 'fresh'):
            target = output / case / arm
            target.mkdir(parents=True)
            for i, path in enumerate(states):
                source = read_source(path)
                original = root / 'panel-pilot' / case / 'km' / 'rep-0' / arm / ('%03d.sig.gz' % i)
                raw = gzip.open(original, 'rt').read()
                transformed = canonical_signature(raw.splitlines(keepends=True), source)
                (target / ('%03d.sig' % i)).write_text(transformed)
                refs = {}
                for reasoner in ('hermit', 'jfact'):
                    ref = root / 'panel-pilot' / case / reasoner / 'rep-0' / 'fresh' / ('%03d.sig.gz' % i)
                    data = gzip.open(ref, 'rb').read()
                    refs[reasoner] = dict(sha256=digest(data), matches=data == transformed.encode('utf-8'))
                rows.append(dict(arm=arm, revision=i, source_sha256=digest(source.encode('utf-8')),
                    original_gzip_sha256=digest(original.read_bytes()), original_signature_sha256=digest(raw.encode('utf-8')),
                    normalized_signature_sha256=digest(transformed.encode('utf-8')), references=refs,
                    original_path=str(original), mapping_only_changed_output=raw != transformed))
    report['summary'] = {case: dict(states=len(rows), matched=sum(all(v['matches'] for v in r['references'].values()) for r in rows),
        mismatches=[dict(arm=r['arm'], revision=r['revision']) for r in rows if not all(v['matches'] for v in r['references'].values())])
        for case, rows in report['cases'].items()}
    (output / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['summary'], sort_keys=True))


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('--audit-controls', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    audit_controls(args.audit_controls, args.out)
