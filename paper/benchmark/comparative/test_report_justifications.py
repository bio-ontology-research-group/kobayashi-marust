import json
from pathlib import Path
import tempfile
import unittest

from report_justifications import measurement_path, report
from run_set import DEFAULT


class ReportTests(unittest.TestCase):
    def test_km_replacement_does_not_replace_rustdl_measurements(self):
        runs = dict(DEFAULT, justifications_km='new', justifications_native='old')
        self.assertIn('java-justifications-new', str(measurement_path(Path('/x'), runs, 'km', 'o', 0, '000')))
        self.assertIn('java-justifications-old', str(measurement_path(Path('/x'), runs, 'rustdl', 'o', 0, '000')))

    def test_reference_failure_is_retained_as_an_ontology_outcome(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root/'workload-selection.json').write_text(json.dumps({'selected': [
                {'ontology': 'failed', 'sha256': 'a'*64}, {'ontology': 'missing', 'sha256': 'b'*64}]}))
            (root/DEFAULT['inventory']).write_text(json.dumps({'artifacts': [{'id': 'km'}, {'id': 'hermit'}]}))
            prepared = root/('prepared-queries-'+DEFAULT['queries_preparation'])/'failed'
            prepared.mkdir(parents=True)
            (prepared/'receipt.json').write_text(json.dumps({'source_sha256': 'a'*64,
                'status': 'query_preparation_failed', 'error': 'frozen_reference_failure: timeout'}))
            result = report(root, 'test', DEFAULT)
            self.assertEqual(result['selected_ontologies'], 2)
            self.assertEqual(result['eligibility']['query_preparation_failed'], 1)
            self.assertEqual(result['eligibility']['missing_preparation'], 1)
            self.assertEqual(result['pairwise'][0]['common_verified_generation_costs']['cases'], 0)
            self.assertEqual(result['sources'][0]['reason'], 'frozen_reference_failure: timeout')


if __name__ == '__main__':
    unittest.main()
