"""Per-phase limits must not consume or restart a retained process."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'oracle/ore'))
import tree_watchdog as watchdog


class SessionWatchdogTests(unittest.TestCase):
    def test_retained_phases_then_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = ('import sys,time\nfrom pathlib import Path\n'
                      'for line in sys.stdin:\n'
                      ' if line.strip()=="hang": time.sleep(20)\n'
                      ' else: Path(line.strip()).write_text("done")\n')
            process = subprocess.Popen([sys.executable, '-c', script], stdin=subprocess.PIPE,
                                       text=True, preexec_fn=watchdog.child_preexec)
            try:
                for index in range(2):
                    marker = root / str(index)
                    process.stdin.write(str(marker) + '\n')
                    process.stdin.flush()
                    result = watchdog.monitor(process, timeout=2, memcap_bytes=256 * 1024**2,
                                              until=marker.exists)
                    self.assertEqual(result.status, 'ready')
                    self.assertIsNone(process.poll())
                    self.assertGreater(result.peak_bytes, 0)
                process.stdin.write('hang\n')
                process.stdin.flush()
                checkpoints = []
                result = watchdog.monitor(process, timeout=.1, memcap_bytes=256 * 1024**2,
                                          until=lambda: False,
                                          on_trip=lambda status, peak: checkpoints.append(status))
                self.assertEqual(result.status, 'timeout')
                self.assertEqual(checkpoints, ['timeout'])
                self.assertIsNotNone(process.poll())
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait()
                process.stdin.close()

    def test_phase_memory_includes_retained_allocations(self):
        with tempfile.TemporaryDirectory() as directory:
            marker = Path(directory) / 'ready'
            script = 'import pathlib,time\nx=bytearray(40*1024*1024)\npathlib.Path(' + repr(str(marker)) + ').touch()\ntime.sleep(20)\n'
            process = subprocess.Popen([sys.executable, '-c', script], preexec_fn=watchdog.child_preexec)
            try:
                first = watchdog.monitor(process, timeout=2, memcap_bytes=128 * 1024**2, until=marker.exists)
                self.assertEqual(first.status, 'ready')
                second = watchdog.monitor(process, timeout=2, memcap_bytes=30 * 1024**2, until=lambda: True)
                self.assertEqual(second.status, 'memout')
                self.assertIsNotNone(process.poll())
            finally:
                if process.poll() is None:
                    process.kill()
                process.wait()


if __name__ == '__main__':
    unittest.main()
