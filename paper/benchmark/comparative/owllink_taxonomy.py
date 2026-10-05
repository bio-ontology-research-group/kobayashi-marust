"""Strict single-revision OWLlink consistency and hierarchy response decoder."""
import xml.etree.ElementTree as ET
from taxonomy import result, TOP, BOTTOM, OWL

NS = 'http://www.owllink.org/owllink#'

def parse(text, expected_classes):
    root = ET.fromstring(text)
    tag = lambda name: '{' + NS + '}' + name
    if root.tag != tag('ResponseMessage'):
        raise ValueError('expected OWLlink ResponseMessage')
    allowed = {tag(x) for x in ['KB', 'OK', 'BooleanResponse', 'ClassHierarchy']}
    if any(e.tag not in allowed for e in root):
        raise ValueError('unexpected or failed OWLlink response')
    booleans = root.findall(tag('BooleanResponse'))
    hierarchies = root.findall(tag('ClassHierarchy'))
    if len(booleans) != 1 or booleans[0].get('result') not in ['true', 'false']:
        raise ValueError('expected exactly one consistency result')
    if booleans[0].get('result') == 'false':
        if hierarchies:
            raise ValueError('unexpected hierarchy for inconsistent revision')
        return result(False, [])
    if len(hierarchies) != 1:
        raise ValueError('expected exactly one complete hierarchy')
    edges, names = [], set()
    def synset(element):
        if element.tag != tag('ClassSynset') or not len(element):
            raise ValueError('invalid class synset')
        group = []
        for child in element:
            if child.tag != '{'+OWL+'}Class' or set(child.attrib) != {'IRI'} or len(child):
                raise ValueError('expected named class with full IRI')
            value = child.attrib['IRI']
            if not value: raise ValueError('empty class IRI')
            group.append(value)
        names.update(group)
        for other in group[1:]:
            edges.extend([(group[0], other), (other, group[0])])
        return group
    hierarchy = hierarchies[0]
    bottoms = [e for e in hierarchy if e.tag == tag('ClassSynset')]
    if len(bottoms) != 1:
        raise ValueError('expected bottom synset')
    unsat = synset(bottoms[0])
    if BOTTOM not in unsat: raise ValueError('bottom synset lacks owl:Nothing')
    for pair in hierarchy:
        if pair is bottoms[0]: continue
        if pair.tag != tag('ClassSubClassesPair') or len(pair) != 2 or pair[1].tag != tag('SubClassSynsets'):
            raise ValueError('invalid hierarchy relation')
        parents = synset(pair[0])
        for child in pair[1]:
            edges.extend((c, p) for c in synset(child) for p in parents)
    expected = set(expected_classes)
    if expected - names - {TOP, BOTTOM} or names - expected - {TOP, BOTTOM}:
        raise ValueError('hierarchy class signature differs from source')
    return result(True, edges, unsat, names)
