from __future__ import annotations

import hashlib
import io
from pathlib import Path
import tarfile
import tempfile
import unittest
import sys


BENCHMARK = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BENCHMARK))
from import_current_final import BASELINES, FINAL_FILES  # noqa: E402
from verify_current_evidence_archive import verify  # noqa: E402


def sha(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def fixture(root: Path, forbidden: bool = False) -> tuple[Path, Path, Path]:
    final = root / "final"
    final.mkdir()
    payloads = {name: f"{name}\n".encode() for name in FINAL_FILES[:-1]}
    records = {}
    for baseline in BASELINES:
        for index in range(189):
            name = f"current-results/{baseline}/o{index:03d}.result.json"
            records[name] = f'{{"baseline":"{baseline}","index":{index}}}\n'.encode()
    record_manifest = "".join(f"{sha(value)}  {name}\n"
                              for name, value in sorted(records.items())).encode()
    payloads["result-records.sha256"] = record_manifest
    for name, value in payloads.items():
        (final / name).write_bytes(value)
    sums = "".join(f"{sha(payloads[name])}  {name}\n" for name in FINAL_FILES).encode()
    (final / "SHA256SUMS").write_bytes(sums)

    archive = root / "evidence.tar.gz"
    with tarfile.open(archive, "w:gz") as package:
        all_files = {"archive/staging/README.md": b"evidence\n"}
        all_files.update(records)
        all_files.update({f"final/{name}": (final / name).read_bytes()
                          for name in (*FINAL_FILES, "SHA256SUMS")})
        if forbidden:
            all_files["runtimes/reasoner.jar"] = b"forbidden"
        for name, value in all_files.items():
            info = tarfile.TarInfo(name)
            info.size = len(value)
            package.addfile(info, io.BytesIO(value))
    sidecar = root / "evidence.tar.gz.sha256"
    sidecar.write_text(f"{hashlib.sha256(archive.read_bytes()).hexdigest()}  {archive.name}\n")
    return archive, sidecar, final


class VerifyCurrentEvidenceArchiveTest(unittest.TestCase):
    def test_complete_archive_rehashes_all_records(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            archive, sidecar, final = fixture(Path(directory))
            report = verify(archive, sidecar, final)
            self.assertEqual(report["result_records"], 1512)

    def test_forbidden_runtime_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            archive, sidecar, final = fixture(Path(directory), forbidden=True)
            with self.assertRaisesRegex(ValueError, "forbidden evidence payload"):
                verify(archive, sidecar, final)


if __name__ == "__main__":
    unittest.main()
