import unittest
from canonical_km import SourceNames, canonical, canonical_signature


class SourceCanonicalizationTests(unittest.TestCase):
    def test_default_named_prefixes_and_iri_preservation(self):
        s = 'Prefix(:=<urn:test:>) Prefix(ex:=<http://example.org/>) Ontology(SubClassOf(:A ex:B) Declaration(Class(<urn:other:C>)))'
        names = SourceNames(s)
        self.assertEqual(names.expand(':A'), 'urn:test:A')
        self.assertEqual(names.expand('ex:B'), 'http://example.org/B')
        self.assertEqual(names.expand('urn:other:C'), 'urn:other:C')
        self.assertEqual(names.expand('urn:test:A'), 'urn:test:A')

    def test_prefix_whitespace_and_quoted_fake_prefix(self):
        s = '# Prefix(:=<urn:bad:>)\nPrefix( : = <urn:right:> ) Ontology(Annotation(<urn:p> "Prefix(:=<urn:wrong:>)") Declaration(Class(:A)))'
        self.assertEqual(SourceNames(s).expand(':A'), 'urn:right:A')

    def test_no_local_name_collision_or_accidental_builtin(self):
        s = 'Prefix(:=<urn:a:>) Prefix(b:=<urn:b:>) Ontology(SubClassOf(:Thing b:Thing))'
        result = dict(dropped=[], consistent=True, unsatisfiable=[], subsumptions=[[':Thing', 'b:Thing']])
        self.assertEqual(canonical(result, s), 'C\ttrue\nS\turn:a:Thing\turn:b:Thing\n')

    def test_builtin_filtering_and_unsat_expansion(self):
        s = 'Prefix(:=<urn:a:>) Ontology(SubClassOf(:A owl:Thing) SubClassOf(:B owl:Nothing))'
        r = dict(dropped=[], consistent=True, unsatisfiable=[':B', 'owl:Nothing'],
                 subsumptions=[[':A', 'owl:Thing'], [':B', ':A'], [':A', ':A']])
        self.assertEqual(canonical(r, s), 'C\ttrue\nU\turn:a:B\n')

    def test_reject_undefined_conflicting_ambiguous_names(self):
        for s in ['Ontology(Declaration(Class(ex:A)))',
                  'Prefix(:=<urn:a:>) Prefix(:=<urn:b:>) Ontology()',
                  'Prefix(urn:=<http://example.org/>) Ontology(Declaration(Class(<urn:A>)) Declaration(Class(urn:A)))']:
            with self.assertRaises(ValueError): SourceNames(s)
        with self.assertRaises(ValueError): SourceNames('Ontology()').expand(':NotInSource')

    def test_alias_deduplication_does_not_invent_transitive_edges(self):
        s = 'Prefix(:=<urn:a:>) Prefix(ex:=<urn:a:>) Ontology(SubClassOf(:A :B) SubClassOf(ex:B ex:C))'
        r = dict(dropped=[], consistent=True, unsatisfiable=[], subsumptions=[[':A', ':B'], ['ex:B', 'ex:C']])
        actual = canonical(r, s)
        self.assertNotIn('S\turn:a:A\turn:a:C', actual)

    def test_map_pairs_and_stable_sort_after_expansion(self):
        s = 'Prefix(z:=<urn:a:>) Prefix(a:=<urn:z:>) Ontology(SubClassOf(z:A z:B) SubClassOf(a:A a:B))'
        r = dict(dropped=[], consistent=True, unsatisfiable=[], subsumptions={'a:A':['a:B'], 'z:A':['z:B']})
        self.assertEqual(canonical(r, s), 'C\ttrue\nS\turn:a:A\turn:a:B\nS\turn:z:A\turn:z:B\n')
        self.assertEqual(canonical_signature(['C\tfalse\n'], s), 'C\tfalse\n')

if __name__ == '__main__': unittest.main()
