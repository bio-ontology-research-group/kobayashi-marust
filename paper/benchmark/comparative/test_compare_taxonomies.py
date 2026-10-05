import unittest
from compare_taxonomies import compare


def record(consistent=True, relation='a'):
    return dict(status='ok', algorithm='full-iri-scc-component-bitset-fingerprint-v1',
                source_sha256='b'*64, source_signature_sha256='c'*64,
                raw_sha256='d'*64, strict_adapter_sha256='e'*64,
                fingerprint_script_sha256='f'*64, relation_sha256=relation*64,
                reported_consistency=consistent)


class ComparisonTests(unittest.TestCase):
    def test_matching_consistent_relations(self):
        self.assertTrue(compare(record(), record())['agreement'])

    def test_taxonomy_and_consistency_disagreements(self):
        self.assertEqual(compare(record(), record(relation='b'))['status'], 'taxonomy_disagreement')
        self.assertEqual(compare(record(), record(False))['status'], 'consistency_disagreement')

    def test_inconsistent_relations_are_not_compared(self):
        result = compare(record(False), record(False, 'b'))
        self.assertTrue(result['agreement'])
        self.assertEqual(result['scope'], 'consistency')

    def test_unknown_consistency_never_becomes_success(self):
        for other in (True, False, None):
            self.assertIsNone(compare(record(None), record(other))['agreement'])
        self.assertTrue(compare(record(None), record())['taxonomy_agreement'])

    def test_different_source_revision_is_rejected(self):
        right = record(); right['source_sha256'] = 'a'*64
        with self.assertRaises(ValueError): compare(record(), right)

    def test_unbound_or_failed_output_is_rejected(self):
        for key, value in [('status', 'error'), ('raw_sha256', None), ('reported_consistency', 1)]:
            right = record(); right[key] = value
            with self.assertRaises(ValueError): compare(record(), right)


if __name__ == '__main__': unittest.main()
