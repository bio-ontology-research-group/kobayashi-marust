import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest
import importlib.util

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('owl_digest', HERE / 'run_four_arm_cleanup_v3.py')
owl = importlib.util.module_from_spec(spec)
spec.loader.exec_module(owl)
eval_spec = importlib.util.spec_from_file_location('owl_digest_evaluator', HERE / 'evaluate_public_owlapi_digest.py')
evaluator = importlib.util.module_from_spec(eval_spec)
eval_spec.loader.exec_module(evaluator)


class OwlDigestTests(unittest.TestCase):
    def write_taxonomy(self, path, lines):
        path.write_text('\n'.join(lines) + '\nZ\tcomplete\n', encoding='utf-8')

    def test_canonical_digest_ignores_row_order_and_compacts(self):
        with tempfile.TemporaryDirectory() as td:
            a = Path(td) / 'a.tsv'
            b = Path(td) / 'b.tsv'
            self.write_taxonomy(a, ['M\tschema\t1', 'M\tclasses\t2', 'M\tunsatisfiable\t1',
                                   'M\tsubsumptions\t1', 'C\ttrue', 'U\turn:A', 'S\turn:A\turn:B'])
            self.write_taxonomy(b, ['S\turn:A\turn:B', 'U\turn:A', 'C\ttrue', 'M\tsubsumptions\t1',
                                   'M\tunsatisfiable\t1', 'M\tclasses\t2', 'M\tschema\t1'])
            va, vb = owl.canonical(a), owl.canonical(b)
            self.assertEqual(va, vb)
            ia, ib = owl.semantic_identity(va), owl.semantic_identity(vb)
            self.assertEqual(ia, ib)
            self.assertEqual(set(ia), {'canonical_sha256', 'consistent', 'unsat_count', 'subsumption_count'})
            self.assertNotIn('subsumptions', ia)
            changed_view = dict(va)
            changed_view['subsumptions'] = [['urn:A', 'urn:C']]
            self.assertNotEqual(ia, owl.semantic_identity(changed_view))

    def test_audit_keeps_only_compact_answer_and_checks_rollback(self):
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            session = base / 'session'
            session.mkdir()
            lines = ['M\tschema\t1', 'M\tclasses\t2', 'M\tunsatisfiable\t0',
                     'M\tsubsumptions\t1', 'C\ttrue', 'S\turn:A\turn:B']
            self.write_taxonomy(session / '000.taxonomy.tsv', lines)
            self.write_taxonomy(session / '001.rollback.taxonomy.tsv', lines)
            attempt = {'arm': 'candidate_retained', 'output': str(base),
                       'measurement': {'revisions': [
                           {'worker': {'status': 'executed_unvalidated', 'dropped_clauses': 0}},
                           {'worker': {'status': 'operation_error', 'exception_message': 'bad update',
                                       'rollback_snapshot_available': True}}]}}
            fixture = {'revisions': [
                {'expected_valid': True},
                {'expected_valid': False, 'expected_error_substring': 'bad update'}]}
            result = owl.audit(attempt, fixture)
            self.assertTrue(all(x['passed'] for x in result), result)
            self.assertIn('semantic_identity', result[0])
            self.assertNotIn('semantic', result[0])
            self.assertNotIn('subsumptions', result[0]['semantic_identity'])
            self.assertEqual(result[0]['semantic_identity'], result[1]['rollback_semantic_identity'])

    def test_evaluator_rejects_missing_nested_cleanup_proof(self):
        top_only = {'remaining_process_tree_or_group': [], 'cleanup_errors': []}
        self.assertFalse(owl.cleanup_is_proven_empty(top_only))
        record = {'remaining_process_tree_or_group': [], 'remaining_processes': [], 'cleanup_errors': [],
                  'child_tree_cleanup': {'status': 'confirmed_empty_after_cleanup',
                                         'remaining_processes': [], 'subreaper_restored': True}}
        self.assertTrue(owl.cleanup_is_proven_empty(record))

    def test_audit_rejects_changed_taxonomy_fact(self):
        with tempfile.TemporaryDirectory() as td:
            base = Path(td); session = base / 'session'; session.mkdir()
            self.write_taxonomy(session / '000.taxonomy.tsv', ['M\tschema\t1', 'M\tclasses\t2',
                'M\tunsatisfiable\t0', 'M\tsubsumptions\t1', 'C\ttrue', 'S\turn:A\turn:C'])
            attempt = {'arm': 'candidate_retained', 'output': str(base),
                       'measurement': {'revisions': [{'worker': {'status': 'executed_unvalidated', 'dropped_clauses': 0}}]}}
            fixture = {'revisions': [{'expected_valid': True, 'entailed': [['urn:A', 'urn:B']]}]}
            result = owl.audit(attempt, fixture)
            self.assertFalse(result[0]['passed'])
            self.assertIn('missing independent entailment', result[0]['error'])

    def test_audit_rejects_rollback_change(self):
        with tempfile.TemporaryDirectory() as td:
            base = Path(td)
            session = base / 'session'
            session.mkdir()
            self.write_taxonomy(session / '000.taxonomy.tsv', ['M\tschema\t1', 'M\tclasses\t1',
                               'M\tunsatisfiable\t0', 'M\tsubsumptions\t0', 'C\ttrue'])
            self.write_taxonomy(session / '001.rollback.taxonomy.tsv', ['M\tschema\t1', 'M\tclasses\t1',
                               'M\tunsatisfiable\t0', 'M\tsubsumptions\t0', 'C\tfalse'])
            attempt = {'arm': 'candidate_retained', 'output': str(base),
                       'measurement': {'revisions': [
                           {'worker': {'status': 'executed_unvalidated', 'dropped_clauses': 0}},
                           {'worker': {'status': 'operation_error', 'exception_message': 'bad update',
                                       'rollback_snapshot_available': True}}]}}
            fixture = {'revisions': [
                {'expected_valid': True},
                {'expected_valid': False, 'expected_error_substring': 'bad update'}]}
            result = owl.audit(attempt, fixture)
            self.assertFalse(result[1]['passed'])
            self.assertIn('rejected update changed', result[1]['error'])


if __name__ == '__main__':
    unittest.main()
