import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('panel_digest', HERE / 'run_panel_cleanup_v3.py')
panel = importlib.util.module_from_spec(spec)
spec.loader.exec_module(panel)


class DigestSemanticsTests(unittest.TestCase):
    def test_cli_digest_preserves_canonical_equality(self):
        a = panel.canonical_result({'consistent': True, 'dropped': 0,
                                    'unsatisfiable': ['urn:B', 'urn:A', 'urn:A'],
                                    'subsumptions': [['urn:A', 'urn:B'], ['urn:A', 'urn:B'], ['urn:B', 'urn:B']]})
        b = panel.canonical_result({'consistent': True, 'dropped': 0,
                                    'unsatisfiable': ['urn:A', 'urn:B'],
                                    'subsumptions': [['urn:B', 'urn:B'], ['urn:A', 'urn:B']]})
        self.assertEqual(a, b)
        self.assertEqual(panel.semantic_digest(a), panel.semantic_digest(b))
        self.assertEqual(set(panel.semantic_digest(a)), {
            'canonical_sha256', 'consistent', 'unsat_count', 'subsumption_count', 'dropped'})
        self.assertNotIn('unsatisfiable', panel.semantic_digest(a))
        self.assertNotIn('nonreflexive_nonunsat_subsumptions', panel.semantic_digest(a))

    def test_cli_digest_changes_for_semantic_change_and_rejects_dropped(self):
        a = panel.canonical_result({'consistent': True, 'dropped': 0, 'unsatisfiable': [], 'subsumptions': []})
        b = panel.canonical_result({'consistent': False, 'dropped': 0, 'unsatisfiable': [], 'subsumptions': []})
        self.assertNotEqual(panel.semantic_digest(a), panel.semantic_digest(b))
        for dropped in (1, True):
            with self.subTest(dropped=dropped), self.assertRaises(ValueError):
                panel.canonical_result({'consistent': True, 'dropped': dropped, 'unsatisfiable': [], 'subsumptions': []})
        with self.assertRaises(ValueError):
            panel.canonical_result({'schema': 'unsupported', 'result': {'consistent': True}})

    def test_digest_changes_when_answer_fact_changes(self):
        a = panel.canonical_result({'consistent': True, 'dropped': 0, 'unsatisfiable': [],
                                    'subsumptions': [['urn:A', 'urn:B']]})
        b = panel.canonical_result({'consistent': True, 'dropped': 0, 'unsatisfiable': [],
                                    'subsumptions': [['urn:A', 'urn:C']]})
        self.assertNotEqual(panel.semantic_digest(a), panel.semantic_digest(b))


if __name__ == '__main__':
    unittest.main()
