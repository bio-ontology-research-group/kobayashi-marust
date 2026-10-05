import json
from pathlib import Path
import unittest

from taxonomy import parse, TOP, BOTTOM


class TaxonomyTests(unittest.TestCase):
    def test_all_ten_real_pilot_outputs(self):
        root = Path(__file__).resolve().parents[3] / 'results/benchmarks/2026-10-04-v1.4.5-comparative/measurement-pilot-53199410'
        folders = [p for p in root.iterdir() if p.is_dir()]
        self.assertEqual(len(folders), 10)
        expected = {('urn:v145:A', 'urn:v145:B'), ('urn:v145:A', 'urn:v145:C'), ('urn:v145:B', 'urn:v145:C')}
        for folder in folders:
            with self.subTest(baseline=folder.name):
                record = json.loads((folder / 'record.json').read_text())
                data = parse((folder / 'taxonomy.raw').read_text(), record['output_format'],
                             prefixes={':': 'urn:v145:'}, expected_classes={'urn:v145:' + c for c in 'ABC'})
                edges = set(map(tuple, data['subsumptions']))
                while True:
                    additional = {(a, d) for a, b in edges for c, d in edges if b == c and a != d}
                    if additional <= edges:
                        break
                    edges |= additional
                edges = {(a, b) for a, b in edges if a not in [TOP, BOTTOM] and b not in [TOP, BOTTOM]}
                self.assertEqual(edges, expected)
                self.assertEqual(data['unsatisfiable'], [])
                self.assertIs(data['consistent'], None if folder.name == 'more' else True)

    def test_truncated_functional_rejected(self):
        with self.assertRaises(ValueError):
            parse('Ontology(SubClassOf(<urn:A> <urn:B>)', 'functional')

    def test_explicit_bottom_is_not_an_unsatisfiable_source_class(self):
        raw = {'consistent': True, 'subsumptions': [],
               'unsatisfiable': [BOTTOM, 'urn:Unsatisfiable']}
        self.assertEqual(parse(json.dumps(raw), 'km-json')['unsatisfiable'],
                         ['urn:Unsatisfiable'])

    def test_unknown_axiom_rejected(self):
        with self.assertRaises(ValueError):
            parse('Ontology(DisjointClasses(<urn:A> <urn:B>))', 'functional')

    def test_prefix_and_fragment_preserved(self):
        data = parse('Prefix(x:=<http://example.org/#>)\nOntology(SubClassOf(x:A x:B))', 'functional')
        self.assertEqual(data['subsumptions'], [['http://example.org/#A', 'http://example.org/#B']])

    def test_unresolved_prefix_rejected(self):
        with self.assertRaises(ValueError):
            parse('Ontology(SubClassOf(x:A x:B))', 'functional')

    def test_source_bound_non_http_iri_is_preserved(self):
        raw = json.dumps({'consistent': True, 'subsumptions': [['EC:1.1.1.1', 'urn:Enzyme']],
                          'unsatisfiable': ['EC:2.2.2.2']})
        expected = {'EC:1.1.1.1', 'EC:2.2.2.2', 'urn:Enzyme'}
        data = parse(raw, 'km-json', prefixes={'EC:': 'urn:unrelated:'}, expected_classes=expected)
        self.assertEqual(data['subsumptions'], [['EC:1.1.1.1', 'urn:Enzyme']])
        self.assertEqual(data['unsatisfiable'], ['EC:2.2.2.2'])
        with self.assertRaises(ValueError):
            parse(raw, 'km-json', expected_classes={'urn:Enzyme'})

    def test_missing_completion_marker_rejected(self):
        with self.assertRaises(ValueError):
            parse('C\ttrue\nS\turn:A\turn:B\n', 'owlapi-tsv')

    def test_conflicting_consistency_rejected(self):
        with self.assertRaises(ValueError):
            parse('C\ttrue\nC\tfalse\nZ\tcomplete\n', 'owlapi-tsv')

    def test_unknown_consistency_not_promoted(self):
        self.assertIsNone(parse('C\tunknown\nZ\tcomplete\n', 'owlapi-tsv')['consistent'])

    def test_incomplete_rustdl_rejected(self):
        raw = {'schema_version': 1, 'consistent': True, 'incomplete': True,
               'direct_subsumptions': [], 'unsatisfiable': [], 'dropped': {}}
        with self.assertRaises(ValueError):
            parse(json.dumps(raw), 'rustdl-json')

    def test_km_dropped_axioms_rejected(self):
        with self.assertRaises(ValueError):
            parse(json.dumps({'consistent': True, 'subsumptions': [], 'unsatisfiable': [], 'dropped': 1}), 'km-json')

    def test_konclude_empty_taxonomy_cannot_cover_nonempty_source(self):
        raw = '<Ontology xmlns="http://www.w3.org/2002/07/owl#"/>'
        with self.assertRaises(ValueError):
            parse(raw, 'owlxml', expected_classes={'urn:A'})

    def test_xml_entity_decoding(self):
        raw = '<Ontology xmlns="http://www.w3.org/2002/07/owl#"><SubClassOf><Class IRI="urn:A&amp;B"/><Class IRI="urn:C"/></SubClassOf></Ontology>'
        self.assertEqual(parse(raw, 'owlxml')['subsumptions'], [['urn:A&B', 'urn:C']])

    def test_serialized_inconsistency_through_equivalence_representative(self):
        xml = '<Ontology xmlns="http://www.w3.org/2002/07/owl#"><EquivalentClasses><Class IRI="urn:A"/><Class abbreviatedIRI="owl:Thing"/><Class abbreviatedIRI="owl:Nothing"/></EquivalentClasses></Ontology>'
        functional = 'Ontology(EquivalentClasses(<urn:A> owl:Thing owl:Nothing))'
        for raw, fmt in [(xml, 'owlxml'), (functional, 'functional')]:
            with self.subTest(format=fmt):
                self.assertIs(parse(raw, fmt)['consistent'], False)

    def test_unsatisfiable_class_does_not_imply_inconsistency(self):
        raw = 'Ontology(EquivalentClasses(<urn:A> owl:Nothing))'
        self.assertIs(parse(raw, 'functional')['consistent'], True)


if __name__ == '__main__':
    unittest.main()
