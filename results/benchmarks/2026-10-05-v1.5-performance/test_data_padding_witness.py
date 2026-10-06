"""Executable rejection tests for the diagnostic source-GCI padding checker."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from check_data_padding_witness import check


class PaddingWitnessTests(unittest.TestCase):
    def test_source_and_witness_mutations(self):
        source = {'concepts': ['A', 'B', 'Parent'], 'source_axioms': [
            {'kind': 'equivalent', 'left': {'Name': 'A'},
             'right': {'Not': {'Name': 'B'}}},
            {'kind': 'sub-class', 'left': {'Name': 'A'}, 'right': {'Name': 'Parent'}},
            {'kind': 'sub-class', 'left': {'Name': 'B'}, 'right': {'Name': 'Parent'}}]}
        witness = {'positive_classes': ['A', 'Parent']}
        cases = [('valid', source, witness, True),
                 ('blank', source, {'positive_classes': []}, False),
                 ('missing-parent', source, {'positive_classes': ['A']}, False),
                 ('both-complements', source, {'positive_classes': ['A', 'B', 'Parent']}, False),
                 ('unknown-class', source, {'positive_classes': ['A', 'Parent', 'C']}, False),
                 ('duplicate-class', source, {'positive_classes': ['A', 'A', 'Parent']}, False),
                 ('extra-witness-field', source, dict(witness, ignore=[0]), False)]

        def appended(name, right, accepted=False, kind='sub-class'):
            changed = copy.deepcopy(source)
            changed['source_axioms'].append({'kind': kind, 'left': {'Name': 'A'}, 'right': right})
            cases.append((name, changed, witness, accepted))

        appended('data-existential', {'Exists': [{'Name': 'd'}, {'Name': '__dt__integer'}]})
        appended('universal-ordinary-role', {'Forall': [{'Name': 'd'}, {'Name': '__dt__integer'}]}, True)
        appended('universal-role', {'Forall': ['Universal', 'Top']})
        appended('negative-cardinality', {'AtLeast': [-1, {'Name': 'r'}, 'Top']})
        appended('hidden-negative-cardinality', {'Forall': [{'Name': 'r'},
                 {'AtMost': [-1, {'Name': 's'}, 'Top']}]})
        appended('unknown-constructor', {'Unsupported': 'A'})
        appended('two-constructors', {'Name': 'A', 'Nominal': 'a'})
        appended('bad-arity', {'Exists': [{'Name': 'r'}, 'Top', 'Bottom']})
        appended('hidden-bad-filler', {'Forall': [{'Name': 'r'}, {'Unsupported': 'A'}]})
        appended('direct-datatype', {'Name': '__dt__integer'})
        appended('self-edge', {'HasSelf': {'Name': 'r'}})
        appended('zero-minimum', {'AtLeast': [0, {'Inverse': 'r'}, 'Top']}, True)
        appended('positive-minimum', {'AtLeast': [1, {'Name': 'r'}, 'Top']})
        appended('disjoint-violation', {'Name': 'Parent'}, kind='disjoint')
        appended('unknown-axiom-kind', 'Top', kind='ignored')
        changed = copy.deepcopy(source)
        changed['source_axioms'][0]['ignore'] = True
        cases.append(('extra-axiom-field', changed, witness, False))
        cases.append(('duplicate-json-key',
                      '{"concepts": [], "source_axioms": [], "source_axioms": []}', witness, False))
        cases.append(('non-json-number', '{"concepts": [], "source_axioms": [], "x": NaN}', witness, False))
        with tempfile.TemporaryDirectory() as tmp:
            for name, input_source, input_witness, expected in cases:
                with self.subTest(name=name):
                    src, wit = Path(tmp) / 'source.json', Path(tmp) / 'witness.json'
                    src.write_text(input_source if isinstance(input_source, str) else json.dumps(input_source))
                    wit.write_text(json.dumps(input_witness))
                    result = check(src, wit)
                    self.assertEqual(result['accepted'], expected, result)
                    print(f'{name}: {"accepted" if expected else "rejected"}', flush=True)


if __name__ == '__main__':
    unittest.main()
