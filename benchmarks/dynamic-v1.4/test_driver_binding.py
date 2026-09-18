"""A measured Java run must identify the compiled bytes, not just source text."""
import hashlib
from pathlib import Path
import tempfile
import unittest
from run_incremental import verify_driver


class DriverBinding(unittest.TestCase):
    def setUp(self):
        temporary_root=Path(__file__).resolve().parents[2]/'.work'/'tmp'
        temporary_root.mkdir(parents=True,exist_ok=True)
        self.directory=tempfile.TemporaryDirectory(dir=temporary_root)
        self.addCleanup(self.directory.cleanup)
        self.root=Path(self.directory.name)
        self.source=self.root/'DynamicBenchmark.java'
        self.source.write_text('source-v1')
        self.bytecode=self.root/'classes/org/kmbenchmark/DynamicBenchmark.class'
        self.bytecode.parent.mkdir(parents=True)
        self.bytecode.write_bytes(b'compiled-v1')
        self.lines=[hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(self.root))
                    for p in [self.source,self.bytecode]]
        self.receipt=self.root/'driver-build.sha256'
        self.receipt.write_text('\n'.join(self.lines)+'\n')

    def test_valid_binding_records_compiled_bytes(self):
        binding=verify_driver(self.root)
        self.assertEqual(len(binding['artifacts']),2)
        self.assertEqual(binding['receipt_sha256'],hashlib.sha256(self.receipt.read_bytes()).hexdigest())

    def test_changed_source_rejected(self):
        self.source.write_text('source-v2')
        with self.assertRaisesRegex(ValueError,'changed after build'):
            verify_driver(self.root)

    def test_changed_class_rejected(self):
        self.bytecode.write_bytes(b'compiled-v2')
        with self.assertRaisesRegex(ValueError,'changed after build'):
            verify_driver(self.root)

    def test_unrecorded_class_rejected(self):
        (self.bytecode.parent/'DynamicBenchmark$1.class').write_bytes(b'extra')
        with self.assertRaisesRegex(ValueError,'class directory'):
            verify_driver(self.root)

    def test_missing_source_binding_rejected(self):
        self.receipt.write_text(self.lines[1]+'\n')
        with self.assertRaisesRegex(ValueError,'omits source'):
            verify_driver(self.root)

    def test_duplicate_record_rejected(self):
        self.receipt.write_text('\n'.join(self.lines+[self.lines[0]])+'\n')
        with self.assertRaisesRegex(ValueError,'duplicate'):
            verify_driver(self.root)


if __name__=='__main__':
    unittest.main()
