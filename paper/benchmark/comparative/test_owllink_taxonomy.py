from pathlib import Path
import unittest
import xml.etree.ElementTree as ET
from owllink_taxonomy import parse, NS

class OWLlinkTests(unittest.TestCase):
    def test_real_retract_restore_responses(self):
        fixture = Path(__file__).resolve().parents[3] / 'results/benchmarks/2026-10-04-v1.4.5-comparative/konclude-owllink-pilot-53202500/response.xml'
        root = ET.parse(fixture).getroot()
        hierarchy = root.findall('{'+NS+'}ClassHierarchy')
        self.assertEqual(len(hierarchy), 3)
        outcomes = []
        for h in hierarchy:
            r = ET.Element('{'+NS+'}ResponseMessage')
            ET.SubElement(r, '{'+NS+'}BooleanResponse', result='true'); r.append(h)
            text = ET.tostring(r, encoding='unicode')
            data = parse(text, ['urn:pilot:'+x for x in 'ABC'])
            self.assertEqual(data['unsatisfiable'], [])
            edges = data['subsumptions']; seen=set(); todo=['urn:pilot:A']
            while todo:
                n=todo.pop()
                if n in seen:continue
                seen.add(n);todo.extend(b for a,b in edges if a==n)
            outcomes.append('urn:pilot:C' in seen)
            with self.assertRaises(ValueError):parse(text,['urn:missing'])
        self.assertEqual(outcomes,[True,False,True])

    def test_missing_or_error_response_is_not_negative_entailment(self):
        for body in ['<Error/>','<BooleanResponse result="true"/>','<BooleanResponse result="unknown"/>']:
            with self.assertRaises(ValueError): parse('<ResponseMessage xmlns="'+NS+'">'+body+'</ResponseMessage>',[])

if __name__ == '__main__': unittest.main()
