import tempfile
from pathlib import Path
import unittest
from owllink_requests import axioms, request

class RequestTests(unittest.TestCase):
    def test_implicit_plain_literal_matches_explicit_default(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'a.xml'; q=Path(directory)/'b.xml'
            for language in ['', ' xml:lang="en"']:
                raw='<Ontology xmlns="http://www.w3.org/2002/07/owl#"><DataPropertyAssertion><DataProperty IRI="urn:p"/><NamedIndividual IRI="urn:a"/><Literal'+language+'>  value  </Literal></DataPropertyAssertion></Ontology>'
                p.write_text(raw)
                q.write_text(raw.replace('<Literal', '<Literal datatypeIRI="http://www.w3.org/1999/02/22-rdf-syntax-ns#PlainLiteral"'))
                before,after=axioms(p),axioms(q)
                self.assertEqual(set(before),set(after))
                literal=next(iter(before.values()))[-1]
                self.assertEqual(literal.text,'  value  ')
                self.assertEqual(literal.get('{http://www.w3.org/XML/1998/namespace}lang'), 'en' if language else None)
                self.assertEqual(request(before,after)[1:],(0,0))

    def test_serialization_prefix_and_whitespace_do_not_create_false_changes(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'a.xml';q=Path(directory)/'b.xml'
            p.write_text('<Ontology xmlns="http://www.w3.org/2002/07/owl#"><Prefix name="x" IRI="urn:x:"/><SubClassOf>\n<Class abbreviatedIRI="x:A"/>\n<Class abbreviatedIRI="x:B"/>\n</SubClassOf></Ontology>')
            q.write_text('<Ontology xmlns="http://www.w3.org/2002/07/owl#"><SubClassOf><Class IRI="urn:x:A"/><Class IRI="urn:x:B"/></SubClassOf></Ontology>')
            before,after=axioms(p),axioms(q)
            self.assertEqual(set(before),set(after))
            _,removed,added=request(before,after)
            self.assertEqual((removed,added),(0,0))
            _,removed,added=request(before,{})
            self.assertEqual((removed,added),(1,0))

    def test_literal_whitespace_is_preserved(self):
        with tempfile.TemporaryDirectory() as directory:
            p=Path(directory)/'a.xml'
            p.write_text('<Ontology xmlns="http://www.w3.org/2002/07/owl#"><DataPropertyAssertion><DataProperty IRI="urn:p"/><NamedIndividual IRI="urn:a"/><Literal datatypeIRI="http://www.w3.org/2001/XMLSchema#string">  </Literal></DataPropertyAssertion></Ontology>')
            self.assertIn('>  </',next(iter(axioms(p))))

if __name__=='__main__':unittest.main()
