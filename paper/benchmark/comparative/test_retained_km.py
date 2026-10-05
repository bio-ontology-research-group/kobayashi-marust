"""Exercise pipe backpressure and interrupted retained sessions."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'oracle/ore'))
from measure_retained_km import measure, digest


class RetainedKMTests(unittest.TestCase):
    def run_case(self, code, source_text, timeout):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source.ofn'
            source.write_text(source_text)
            binary = root / 'worker'
            binary.write_text('#!' + sys.executable + '\n' + code)
            binary.chmod(0o755)
            revision = {'path': str(source), 'sha256': digest(source)}
            return measure({'path': str(binary), 'sha256': digest(binary)}, [revision, revision],
                           root / 'output', timeout=timeout)

    def test_source_larger_than_pipe_buffer(self):
        code = ('import sys,json\nfor line in sys.stdin:\n'
                ' request=json.loads(line)\n'
                ' print(json.dumps({"status":"ok","result":{"bytes":len(request["functional_syntax"])}}),flush=True)\n')
        result = self.run_case(code, 'x' * (4 * 1024**2), 5)
        self.assertEqual(result['status'], 'executed_unvalidated', result)
        self.assertTrue(all(r['wall_s'] < 5 for r in result['revisions']))

    def test_stalled_reader_is_killed_and_later_revision_is_visible(self):
        result = self.run_case('import time\ntime.sleep(20)\n', 'x' * (4 * 1024**2), .2)
        self.assertEqual(result['status'], 'timeout', result)
        self.assertEqual(result['revisions'][0]['status'], 'timeout')
        self.assertEqual(result['revisions'][1]['status'], 'not_run_after_session_failure')


if __name__ == '__main__':
    unittest.main()
