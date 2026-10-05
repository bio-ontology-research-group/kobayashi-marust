"""Strict adapters for the pinned baseline taxonomy formats.

Return direct named-class edges for the existing full-IRI closure/fingerprint
tool. Do not infer missing consistency or silently accept dropped axioms.
"""
import json
import re
import xml.etree.ElementTree as ET

OWL = 'http://www.w3.org/2002/07/owl#'
TOP, BOTTOM = OWL + 'Thing', OWL + 'Nothing'


def resolve(value, prefixes, expected_classes=None):
    if not isinstance(value, str) or not value:
        raise ValueError('invalid class identifier')
    # A source signature may contain absolute IRIs with non-HTTP schemes
    # (for example EC:1.1.1.1). Preserve an exact source IRI before treating
    # its scheme-like prefix as an abbreviated name.
    if expected_classes is not None and value in expected_classes:
        return value
    if value.startswith('<') and value.endswith('>'):
        return value[1:-1]
    prefix, separator, suffix = value.partition(':')
    if separator and prefix + ':' in prefixes:
        return prefixes[prefix + ':'] + suffix
    if prefix in ['http', 'https', 'urn', 'ftp', 'file'] and separator:
        return value
    raise ValueError('unresolved class identifier: ' + value)


def result(consistent, edges, unsat=(), declared=None):
    if consistent not in (True, False, None):
        raise ValueError('invalid consistency field')
    return {'consistent': consistent, 'subsumptions': [list(p) for p in sorted(set(edges))],
            # The comparison contract lists unsatisfiable source classes.
            # OWLlink includes owl:Nothing in every bottom synset; other
            # serializers omit it. It is not an additional inferred result.
            'unsatisfiable': sorted(set(unsat) - {BOTTOM}),
            'declared': None if declared is None else sorted(set(declared))}


def parse_json(text, baseline, prefixes, expected_classes=None):
    data = json.loads(text)
    if type(data.get('consistent')) is not bool:
        raise ValueError('missing boolean consistency')
    if baseline == 'rustdl' and data.get('schema_version') != 1:
        raise ValueError('unexpected RustDL schema')
    if data.get('incomplete', False) or data.get('dropped'):
        raise ValueError('incomplete reasoning or dropped axioms')
    if baseline == 'rustdl' and data.get('incomplete') is not False:
        raise ValueError('missing completeness declaration')
    key = 'direct_subsumptions' if baseline == 'rustdl' else 'subsumptions'
    if not isinstance(data.get(key), list) or not isinstance(data.get('unsatisfiable'), list):
        raise ValueError('missing taxonomy arrays')
    edges = []
    for pair in data[key]:
        if not isinstance(pair, list) or len(pair) != 2:
            raise ValueError('malformed subclass pair')
        edges.append(tuple(resolve(x, prefixes, expected_classes) for x in pair))
    for group in data.get('equivalent_groups', []):
        if not isinstance(group, list) or len(group) < 2:
            raise ValueError('malformed equivalence group')
        names = [resolve(x, prefixes, expected_classes) for x in group]
        for other in names[1:]:
            edges.extend([(names[0], other), (other, names[0])])
    return result(data['consistent'], edges, [resolve(x, prefixes, expected_classes) for x in data['unsatisfiable']])


def parse_tsv(text):
    lines = text.splitlines()
    if not lines or lines[-1] != 'Z\tcomplete':
        raise ValueError('missing taxonomy completion marker')
    consistency = []
    edges, unsat = [], []
    for line in lines[:-1]:
        fields = line.split('\t')
        if fields[0] == 'M' and len(fields) == 3:
            continue
        if fields[0] == 'C' and len(fields) == 2 and fields[1] in ['true', 'false', 'unknown']:
            consistency.append({'true': True, 'false': False, 'unknown': None}[fields[1]])
        elif fields[0] == 'S' and len(fields) == 3:
            edges.append(tuple(fields[1:]))
        elif fields[0] == 'U' and len(fields) == 2:
            unsat.append(fields[1])
        else:
            raise ValueError('unexpected taxonomy record')
    if len(consistency) != 1:
        raise ValueError('expected exactly one consistency record')
    # These records are emitted by the pinned OWLAPI full-IRI writer.
    if any(not x or ':' not in x for p in edges for x in p) or any(':' not in x for x in unsat):
        raise ValueError('non-IRI in full-IRI records')
    return result(consistency[0], edges, unsat)


def serialized_taxonomy_result(edges, declared):
    # Taxonomy serializations encode inconsistency as Thing <= Nothing,
    # possibly through other members of an equivalence group.
    successors = {}
    for left, right in edges:
        successors.setdefault(left, []).append(right)
    seen, pending = set(), [TOP]
    while pending:
        node = pending.pop()
        if node == BOTTOM:
            return result(False, edges, declared=declared)
        if node not in seen:
            seen.add(node)
            pending.extend(successors.get(node, ()))
    return result(True, edges, declared=declared)


def parse_xml(text):
    root = ET.fromstring(text)
    if root.tag != '{' + OWL + '}Ontology':
        raise ValueError('expected OWL/XML ontology')
    prefixes = {'owl:': OWL}
    for node in root:
        if node.tag == '{' + OWL + '}Prefix':
            prefixes[node.attrib['name'].rstrip(':') + ':'] = node.attrib['IRI']
    def cls(node):
        if node.tag != '{' + OWL + '}Class' or len(node):
            raise ValueError('taxonomy contains a class expression')
        if 'IRI' in node.attrib:
            return node.attrib['IRI']
        return resolve(node.attrib['abbreviatedIRI'], prefixes)
    edges, declared = [], set()
    for node in root:
        kind = node.tag.removeprefix('{' + OWL + '}')
        if kind in ['Prefix', 'Annotation']:
            continue
        if kind == 'Declaration' and len(node) == 1:
            declared.add(cls(node[0]))
        elif kind == 'SubClassOf' and len(node) == 2:
            edges.append((cls(node[0]), cls(node[1])))
        elif kind == 'EquivalentClasses' and len(node) >= 2:
            names = [cls(n) for n in node]
            for other in names[1:]:
                edges.extend([(names[0], other), (other, names[0])])
        else:
            raise ValueError('unexpected taxonomy axiom: ' + kind)
    return serialized_taxonomy_result(edges, declared)


TOKEN = re.compile(r'\s+|\#[^\n]*|<[^<>]*>|"(?:[^"\\]|\\.)*"|[()]|[^\s()<>"#]+')


def parse_functional(text):
    tokens = []
    offset = 0
    for match in TOKEN.finditer(text):
        if match.start() != offset:
            raise ValueError('invalid taxonomy token')
        offset = match.end()
        token = match.group()
        if not token.isspace() and not token.startswith('#'):
            tokens.append(token)
    if offset != len(text):
        raise ValueError('truncated taxonomy token')
    position = 0
    def expression():
        nonlocal position
        if position >= len(tokens) or tokens[position] in ['(', ')']:
            raise ValueError('malformed taxonomy expression')
        name = tokens[position]
        position += 1
        if position == len(tokens) or tokens[position] != '(':
            return name
        position += 1
        children = []
        while position < len(tokens) and tokens[position] != ')':
            children.append(expression())
        if position == len(tokens):
            raise ValueError('unclosed taxonomy expression')
        position += 1
        return [name, *children]
    roots = []
    while position < len(tokens):
        roots.append(expression())
    prefixes = {'owl:': OWL}
    ontology = None
    for node in roots:
        if isinstance(node, list) and node[0] == 'Prefix' and len(node) == 3:
            if not isinstance(node[1], str) or not node[1].endswith(':='):
                raise ValueError('malformed prefix binding')
            if not isinstance(node[2], str) or not node[2].startswith('<'):
                raise ValueError('malformed prefix IRI')
            prefixes[node[1][:-1]] = node[2][1:-1]
        elif isinstance(node, list) and node[0] == 'Ontology' and ontology is None:
            ontology = node[1:]
        else:
            raise ValueError('unexpected top-level taxonomy expression')
    if ontology is None:
        raise ValueError('missing ontology')
    edges, declared = [], set()
    axiom_seen = False
    headers = 0
    for node in ontology:
        if isinstance(node, str) and not axiom_seen and node.startswith('<') and headers < 2:
            headers += 1
            continue
        axiom_seen = True
        if not isinstance(node, list):
            raise ValueError('unexpected ontology token')
        if node[0] == 'Annotation':
            continue
        if node[0] == 'Declaration' and len(node) == 2:
            cls = node[1]
            if not isinstance(cls, list) or len(cls) != 2 or cls[0] != 'Class':
                raise ValueError('unexpected declaration')
            declared.add(resolve(cls[1], prefixes))
        elif node[0] == 'SubClassOf' and len(node) == 3:
            edges.append((resolve(node[1], prefixes), resolve(node[2], prefixes)))
        elif node[0] == 'EquivalentClasses' and len(node) >= 3:
            names = [resolve(x, prefixes) for x in node[1:]]
            for other in names[1:]:
                edges.extend([(names[0], other), (other, names[0])])
        else:
            raise ValueError('unexpected taxonomy axiom: ' + node[0])
    return serialized_taxonomy_result(edges, declared)


def parse(text, output_format, prefixes=None, expected_classes=None):
    if output_format in ['km-json', 'rustdl-json']:
        data = parse_json(text, output_format.split('-')[0], dict({'owl:': OWL}, **(prefixes or {})), expected_classes)
    elif output_format == 'owlapi-tsv':
        data = parse_tsv(text)
    elif output_format == 'owlxml':
        data = parse_xml(text)
    elif output_format == 'functional':
        data = parse_functional(text)
    else:
        raise ValueError('unknown taxonomy format')
    if expected_classes is not None and data['declared'] is not None:
        missing = set(expected_classes) - set(data['declared']) - {TOP, BOTTOM}
        if missing:
            raise ValueError('taxonomy omits source classes: ' + str(len(missing)))
    return data
