import json
from pathlib import Path
import tempfile
import unittest

from report_updates import measurement_path, report
from run_set import DEFAULT


class ReportTests(unittest.TestCase):
    def test_preparation_failures_keep_all_revision_denominators(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'workload-selection.json').write_text(json.dumps({'selected': [
                {'ontology': 'failed', 'sha256': 'a'*64}]}))
            (root/DEFAULT['inventory']).write_text(json.dumps({'artifacts': [
                {'id': b} for b in ['km', 'rustdl']]}))
            prepared = root/('prepared-updates-'+DEFAULT['updates_preparation'])/'failed'
            prepared.mkdir(parents=True)
            (prepared/'receipt.json').write_text(json.dumps({'source_sha256': 'a'*64,
                'status': 'preparation_timeout'}))
            result = report(root, 'test', DEFAULT)
            self.assertEqual(result['selected_ontologies'], 1)
            self.assertEqual(result['coverage_per_revision_repetition']['km-cold']['preparation_failed'], 15)
            self.assertNotIn('rustdl-retained', result['coverage_per_revision_repetition'])
            for pair in result['pairwise']:
                self.assertEqual(pair['outcomes']['comparison_unavailable'], 3 if pair['phase']=='initialization' else 12)
                self.assertEqual(pair['costs_on_fully_agreeing_cases']['cases'], 0)

    def test_retained_and_fresh_konclude_paths_are_distinct(self):
        cold = measurement_path(Path('/x'), DEFAULT, 'konclude', 'cold', 'o', 2, 4)
        retained = measurement_path(Path('/x'), DEFAULT, 'konclude', 'retained', 'o', 2, 4)
        self.assertEqual(cold.name, '004')
        self.assertEqual(retained.name, 'repetition-2')
        self.assertIn('konclude-retained-', str(retained))


if __name__ == '__main__':
    unittest.main()
