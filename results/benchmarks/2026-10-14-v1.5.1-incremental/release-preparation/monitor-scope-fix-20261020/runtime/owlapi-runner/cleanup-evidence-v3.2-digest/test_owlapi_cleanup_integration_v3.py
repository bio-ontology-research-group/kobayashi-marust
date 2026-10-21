"""Process-only integration checks for versioned OWLAPI cleanup; no Java/KM run."""
import json
import os
from pathlib import Path
import tempfile
import textwrap
import unittest
from unittest import mock

import measure_public_owlapi_cleanup_v3 as measurement


WORKER = r'''#!/usr/bin/env python3
import json, os, pathlib, subprocess, sys
session = pathlib.Path(sys.argv[11])
session.mkdir(parents=True, exist_ok=True)
print("READY", flush=True)
for line in sys.stdin:
    index = 0
    (session / f"{index:03}.timing.json").write_text(json.dumps({"status":"executed_unvalidated","dropped_clauses":0}))
    print(f"DONE\t{index}\texecuted_unvalidated", flush=True)
print("COMPLETE", flush=True)
pidfile = os.environ.get("OWL_CLEANUP_TEST_PIDFILE")
if pidfile:
    child = "import time; time.sleep(60)"
    spawned = subprocess.Popen([sys.executable, "-c", child], start_new_session=True)
    pathlib.Path(pidfile).write_text(str(spawned.pid))
'''


class OwlApiCleanupIntegrationTests(unittest.TestCase):
    def test_escaped_grandchild_is_found_after_root_exits(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            worker = root / 'fake-java'
            worker.write_text(WORKER)
            worker.chmod(0o755)
            source = root / 'revision.ofn'
            source.write_text('Ontology()\n')
            pidfile = root / 'escaped.pid'
            old = os.environ.get('OWL_CLEANUP_TEST_PIDFILE')
            os.environ['OWL_CLEANUP_TEST_PIDFILE'] = str(pidfile)
            try:
                cpu = min(os.sched_getaffinity(0))
                started = __import__('time').monotonic()
                # Force the legacy tree/group sampler to miss every child;
                # the subreaper ancestry proof must still release inherited
                # stdout and reap the setsid grandchild.
                with mock.patch.object(measurement.watchdog, 'tree_and_group_rss', return_value=(0, [])):
                    result = measurement.measure(
                        {'java': str(worker), 'binary': '/unused/km', 'classpath': '/unused/classes'},
                        [{'path': str(source)}], 'retained', root / 'out', cpu,
                        timeout=10, memory_mib=256, heap='128m')
                elapsed = __import__('time').monotonic() - started
            finally:
                if old is None:
                    os.environ.pop('OWL_CLEANUP_TEST_PIDFILE', None)
                else:
                    os.environ['OWL_CLEANUP_TEST_PIDFILE'] = old
            self.assertEqual(result['actual_exit_code'], 0, result)
            self.assertEqual(result['status'], 'executed_unvalidated', result)
            cleanup = result['child_tree_cleanup']
            self.assertEqual(cleanup['status'], 'confirmed_empty_after_cleanup', cleanup)
            self.assertEqual(cleanup['remaining_processes'], [], cleanup)
            self.assertTrue(cleanup['subreaper_restored'], cleanup)
            escaped = int(pidfile.read_text())
            self.assertIn(escaped, [row['pid'] for row in cleanup['signaled_processes']], cleanup)
            self.assertNotIn(str(escaped), result['tracked_process_start_and_group'])
            self.assertLess(elapsed, 4.5, 'stdout reader may have waited until its join timeout')
            with self.assertRaises(ProcessLookupError):
                os.kill(escaped, 0)
            self.assertEqual(result['remaining_processes'], [])

    def test_preflight_delay_is_outside_launch_to_ready_timer(self):
        original = measurement.SubreaperScope.begin
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            worker = root / 'fake-java'
            worker.write_text(WORKER)
            worker.chmod(0o755)
            source = root / 'revision.ofn'
            source.write_text('Ontology()\n')
            def delayed_begin(scope):
                import time
                time.sleep(0.2)
                return original(scope)
            with mock.patch.object(measurement.SubreaperScope, 'begin', delayed_begin):
                cpu = min(os.sched_getaffinity(0))
                result = measurement.measure(
                    {'java': str(worker), 'binary': '/unused/km', 'classpath': '/unused/classes'},
                    [{'path': str(source)}], 'retained', root / 'out', cpu,
                    timeout=10, memory_mib=256, heap='128m')
            self.assertGreaterEqual(result['cleanup_preflight_wall_s'], 0.19, result)
            self.assertLess(result['launch_to_ready_wall_s'], 0.19, result)
            self.assertEqual(result['child_tree_cleanup']['status'], 'confirmed_empty_after_cleanup', result)

    def test_setup_failure_never_claims_cleanup_success(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / 'revision.ofn'
            source.write_text('Ontology()\n')
            with mock.patch.object(measurement.SubreaperScope, 'begin', side_effect=RuntimeError('synthetic setup failure')):
                cpu = min(os.sched_getaffinity(0))
                result = measurement.measure(
                    {'java': '/no-such-worker', 'binary': '/unused/km', 'classpath': '/unused/classes'},
                    [{'path': str(source)}], 'retained', root / 'out', cpu,
                    timeout=1, memory_mib=256, heap='128m')
            self.assertNotEqual(result['status'], 'executed_unvalidated')
            self.assertIsNone(result['remaining_processes'])
            self.assertIsNone(result['child_tree_cleanup']['remaining_processes'])
            self.assertFalse(result['child_tree_cleanup']['subreaper_restored'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
