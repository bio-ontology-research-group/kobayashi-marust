"""Import the frozen driver and its delayed reporting dependency without measuring."""
import hashlib
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parent

class RuntimePackagingTest(unittest.TestCase):
    def test_driver_and_delayed_evaluator_are_shipped(self):
        runtime = ROOT / "runtime"
        for path in (runtime / "timing-runner", runtime / "owlapi-runner", runtime / "owlapi-runner/cleanup-evidence-v3.2-digest"):
            sys.path.insert(0, str(path))
        spec = importlib.util.spec_from_file_location("frozen_driver", ROOT / "run_shard.py")
        driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(driver)
        from evaluate_public_owlapi_digest import evaluate
        self.assertTrue(callable(driver.measure))
        self.assertTrue(callable(evaluate))
        evaluator = runtime / "owlapi-runner/cleanup-evidence-v3.2-digest/evaluate_public_owlapi_digest.py"
        self.assertEqual(hashlib.sha256(evaluator.read_bytes()).hexdigest(), "f816d7ce2d94978e7d8ee4b5295576d96c7998a0f263868030bd42b5cea245cb")

if __name__ == "__main__":
    unittest.main()
