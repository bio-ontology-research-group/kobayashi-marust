import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).parents[1] / "runners" / "validate_result.py"
SPEC = importlib.util.spec_from_file_location("validate_result", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ValidateResultTest(unittest.TestCase):
    def make_terminal_error(self, root: Path, baseline: str) -> tuple[Path, Path, Path, Path]:
        ontology = root / "example.ofn"
        ontology.write_text("Ontology(<urn:test>)\n", encoding="utf-8")
        runtime = root / ("km" if baseline == "km" else "reasoner.jar")
        runtime.write_bytes(b"runtime")
        runner = root / "runner.py"
        runner.write_text("# runner\n", encoding="utf-8")
        stderr = root / "example.stderr"
        stderr.write_text("expected error\n", encoding="utf-8")
        result = root / "example.result.json"
        record = {
            "schema": 1,
            "baseline": baseline,
            "ontology_id": "example",
            "ontology_sha256": digest(ontology),
            "runtime_sha256" if baseline != "km" else "binary_sha256": digest(runtime),
            "runner_sha256": digest(runner),
            "status": "error",
            "checkpointed": True,
            "wall_s": 0.1,
            "peak_mb": 1.0,
            "rc": 1,
            "stderr_sha256": digest(stderr),
        }
        result.write_text(json.dumps(record), encoding="utf-8")
        return result, ontology, runtime, runner

    def invoke(self, result: Path, ontology: Path, runtime: Path, runner: Path,
               baseline: str) -> None:
        argv = [
            "validate_result.py", "--result", str(result), "--baseline", baseline,
            "--ontology-id", "example", "--ontology", str(ontology),
            "--runtime", str(runtime), "--runner", str(runner),
        ]
        with mock.patch("sys.argv", argv):
            MODULE.main()

    def test_java_record_does_not_require_redundant_input_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = self.make_terminal_error(Path(directory), "jfact")
            self.invoke(*paths, "jfact")

    def test_native_record_requires_runtime_input_digest(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = self.make_terminal_error(Path(directory), "km")
            with self.assertRaisesRegex(ValueError, "runtime ontology serialization digest mismatch"):
                self.invoke(*paths, "km")


if __name__ == "__main__":
    unittest.main()
