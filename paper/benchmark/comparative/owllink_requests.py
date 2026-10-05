"""Preserve OWL/XML axiom identities when building retained-session changes."""
import xml.etree.ElementTree as ET
from pathlib import Path
from owllink_taxonomy import NS
from taxonomy import OWL


def axioms(path):
    root = ET.parse(path).getroot()
    if root.tag != '{'+OWL+'}Ontology': raise ValueError('expected OWL/XML ontology')
    prefixes = {e.get('name')+':': e.get('IRI') for e in root if e.tag == '{'+OWL+'}Prefix'}
    def expand(value):
        prefix, sep, suffix = value.partition(':')
        if not sep or prefix+':' not in prefixes: raise ValueError('unbound OWL/XML prefix')
        return prefixes[prefix+':'] + suffix
    output = {}
    for axiom in root:
        if axiom.tag == '{'+OWL+'}Prefix': continue
        if axiom.tag == '{'+OWL+'}Import': raise ValueError('unfrozen imports')
        # Ontology annotations have no logical effect and are not OWLlink Tell axioms.
        if axiom.tag == '{'+OWL+'}Annotation': continue
        for e in axiom.iter():
            # Konclude's OWLlink DOM parser lacks the file parser's default
            # for plain literals. Spell out that OWL/XML default so both
            # interfaces receive the same datatype, including xml:lang.
            if e.tag == '{'+OWL+'}Literal' and 'datatypeIRI' not in e.attrib:
                e.set('datatypeIRI', 'http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral')
            if 'abbreviatedIRI' in e.attrib: e.set('IRI', expand(e.attrib.pop('abbreviatedIRI')))
            if e.tag == '{'+OWL+'}AbbreviatedIRI':
                e.tag = '{'+OWL+'}IRI'; e.text = expand(e.text)
            e.attrib = dict(sorted(e.attrib.items()))
            # Preserve lexical literal whitespace; discard serializer indentation only.
            if e.tag != '{'+OWL+'}Literal' and e.text is not None and not e.text.strip(): e.text = None
            e.tail = None
        serialized = ET.tostring(axiom, encoding='unicode')
        output[serialized] = axiom
    return output


def request(previous, current, initial=False):
    root = ET.Element('{'+NS+'}RequestMessage')
    kb = {'kb':'urn:km:v145:retained'}
    if initial: ET.SubElement(root,'{'+NS+'}CreateKB',kb)
    removed, added = sorted(previous.keys()-current.keys()), sorted(current.keys()-previous.keys())
    for command, keys, mapping in [('Retract',removed,previous),('Tell',added,current)]:
        if keys:
            node = ET.SubElement(root,'{'+NS+'}'+command,kb)
            for key in keys: node.append(mapping[key])
    ET.SubElement(root,'{'+NS+'}IsKBSatisfiable',kb)
    return ET.tostring(root,encoding='utf-8',xml_declaration=True), len(removed), len(added)


def hierarchy_request():
    root=ET.Element('{'+NS+'}RequestMessage')
    ET.SubElement(root,'{'+NS+'}GetSubClassHierarchy',kb='urn:km:v145:retained')
    return ET.tostring(root,encoding='utf-8',xml_declaration=True)
