"""Exercise resource enforcement and failure preservation without a reasoner."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'oracle/ore'))
from measure_classification import digest, measure


class MeasurementTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.source = self.root / 'source.ofn'
        self.source.write_text('Ontology()\n')

    def tearDown(self):
        self.tmp.cleanup()

    def run_worker(self, code, **kwargs):
        worker = self.root / 'worker'
        worker.write_text('#!' + sys.executable + '\n' + code)
        worker.chmod(0o755)
        inventory = {'artifacts': [{'id': 'km', 'path': str(worker), 'sha256': digest(worker)}]}
        return measure(inventory, 'km', self.source, kwargs.pop('source_hash', digest(self.source)),
                       self.root / 'output', **kwargs)

    def test_success_is_not_semantic_validation(self):
        result = self.run_worker('import os,json\nprint(json.dumps({"affinity":len(os.sched_getaffinity(0)),"threads":os.environ["KM_THREADS"]}))\n')
        self.assertEqual(result['status'], 'executed_unvalidated')
        self.assertEqual(result['semantic_validation'], 'pending')
        data = json.loads((self.root / 'output/taxonomy.raw').read_text())
        self.assertEqual(data, {'affinity': 1, 'threads': '1'})
        self.assertGreater(result['peak_bytes'], 0)

    def test_wrong_source_never_executes(self):
        result = self.run_worker('raise AssertionError("must not execute")\n', source_hash='0' * 64)
        self.assertEqual(result['status'], 'adapter_error')
        self.assertIn('source hash mismatch', result['error'])
        self.assertNotIn('exit_code', result)

    def test_exit_failure_keeps_output(self):
        result = self.run_worker('import sys\nprint("partial output")\nsys.exit(7)\n')
        self.assertEqual(result['exit_code'], 7)
        self.assertNotEqual(result['status'], 'executed_unvalidated')
        self.assertIn('partial output', (self.root / 'output/taxonomy.raw').read_text())

    def test_timeout_is_terminal_and_persisted(self):
        result = self.run_worker('import time\ntime.sleep(10)\n', timeout=.1)
        self.assertEqual(result['status'], 'timeout')
        saved = json.loads((self.root / 'output/record.json').read_text())
        self.assertEqual(saved['status'], 'timeout')
        self.assertIsNotNone(saved['exit_code'])


if __name__ == '__main__':
    unittest.main()
