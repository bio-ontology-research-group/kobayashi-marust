import json
from pathlib import Path
import tempfile
import unittest

from report_classification import paired_costs, report
from run_set import DEFAULT


class ReportTests(unittest.TestCase):
    def test_ratios_are_paired_not_ratio_of_independent_medians(self):
        pairs = [({'wall_s': a}, {'wall_s': b}) for a, b in [(1, 2), (10, 100), (100, 200)]]
        result = paired_costs(pairs)
        self.assertEqual(result['cases'], 3)
        self.assertEqual(result['wall_s']['median_paired_ratio'], 2)
        self.assertEqual(result['peak_bytes']['measured_pairs'], 0)

    def test_absent_and_invalid_costs_are_not_imputed(self):
        result = paired_costs([({}, {}), ({'wall_s': 0}, {'wall_s': 1}),
                               ({'wall_s': float('nan')}, {'wall_s': 2})])
        self.assertEqual(result['cases'], 3)
        self.assertEqual(result['wall_s']['measured_pairs'], 0)
        self.assertNotIn('median_paired_ratio', result['wall_s'])

    def test_missing_and_failed_inputs_remain_in_denominator(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps({'inputs': [
                {'ontology': 'valid', 'sha256': 'a'*64, 'input_admission': 'valid_input'},
                {'ontology': 'invalid', 'sha256': 'b'*64, 'input_admission': 'invalid_input'}]}))
            (root / DEFAULT['inventory']).write_text(json.dumps({'artifacts': [
                {'id': b, 'sha256': 'c'*64} for b in ['km', 'hermit']]}))
            path = root / ('classification-' + DEFAULT['classification_km']) / 'km' / 'invalid'
            path.mkdir(parents=True)
            (path / 'record.json').write_text(json.dumps({'source_sha256': 'b'*64,
                'artifact_sha256': 'c'*64, 'status': 'process_error'}))
            result = report(root, 'test', manifest, DEFAULT)
            self.assertEqual(result['expected_inputs'], 2)
            self.assertEqual(result['coverage']['km']['invalid_input:process_error'], 1)
            self.assertEqual(result['coverage']['km']['valid_input:missing_measurement'], 1)
            self.assertEqual(result['pairwise'][0]['outcomes']['comparison_unavailable'], 2)
            self.assertEqual(result['pairwise'][0]['costs_on_valid_fully_agreeing_cases']['cases'], 0)


if __name__ == '__main__':
    unittest.main()
