import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("assets", Path(__file__).with_name("release_assets.py"))
a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)
C = "1" * 40


def fixture(commit=C):
    blobs = {name: (name + "\n").encode() for name in a.NAMES if name != "SHA256SUMS"}
    blobs["SHA256SUMS"] = "".join(hashlib.sha256(data).hexdigest() + "  " + name + "\n"
                                  for name, data in blobs.items()).encode()
    doc = {"schema": "km-release-assets-v1", "tag": a.TAG, "commit": commit,
           "assets": [{"name": name, "size": len(data), "sha256": hashlib.sha256(data).hexdigest()}
                      for name, data in blobs.items()]}
    raw = json.dumps(doc).encode()
    sha = hashlib.sha256(raw).hexdigest()
    return blobs, doc, raw, sha, a.PREFIX + commit + "/" + sha + "/manifest.json"


class IntegrityTests(unittest.TestCase):
    def test_tag_pointer_binds_exact_commit_origin_and_single_field(self):
        _, _, _, sha, url = fixture()
        header = "object " + C + "\ntype commit\ntag v1.5.1\ntagger Release <n@example.org> 1 +0000\n\n"
        message = "KM-Release-Manifest: " + url
        self.assertEqual(a.tag_pointer(header + message, C), (url, sha))
        bad = [message + "\n" + message, message.replace("https:", "http:"),
               message.replace("leechuck.de", "leechuck.de.evil.test"),
               message.replace("/manifest.json", "/../manifest.json"),
               message.replace(C, "2" * 40), message + "?token=x", "ordinary tag notes"]
        for value in bad:
            with self.subTest(value=value), self.assertRaises(ValueError):
                a.tag_pointer(header + value, C)

    def test_manifest_hash_duplicate_keys_and_identity(self):
        _, doc, raw, sha, _ = fixture()
        self.assertEqual(set(a.manifest_rows(raw, sha, C)), set(a.NAMES))
        with self.assertRaises(ValueError):
            a.manifest_rows(raw + b" ", sha, C)
        for key, value in [("commit", "2" * 40), ("tag", "v1.5.0"), ("schema", "other")]:
            altered = dict(doc, **{key: value}); body = json.dumps(altered).encode()
            with self.subTest(key=key), self.assertRaises(ValueError):
                a.manifest_rows(body, hashlib.sha256(body).hexdigest(), C)
        body = raw[:-1] + b',"tag":"v1.5.1"}'
        with self.assertRaises(ValueError):
            a.manifest_rows(body, hashlib.sha256(body).hexdigest(), C)

    def test_manifest_rejects_missing_duplicate_unlisted_and_excessive_assets(self):
        _, doc, _, _, _ = fixture()
        alterations = [doc["assets"][:-1], doc["assets"][:3] + [doc["assets"][0]]]
        for name, size in [("../payload", 1), ("other.zip", 1), ("build-completion.json", True),
                           ("build-completion.json", (8 << 20) + 1)]:
            rows = [dict(row) for row in doc["assets"]]
            rows[0].update(name=name, size=size); alterations.append(rows)
        for rows in alterations:
            raw = json.dumps(dict(doc, assets=rows)).encode()
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                a.manifest_rows(raw, hashlib.sha256(raw).hexdigest(), C)

    def test_checksums_bind_other_assets_without_self_reference(self):
        blobs, _, raw, sha, _ = fixture(); rows = a.manifest_rows(raw, sha, C)
        a.checksum_rows(blobs["SHA256SUMS"], rows)
        for body in [b"", blobs["SHA256SUMS"] * 2,
                     blobs["SHA256SUMS"].replace(b"km-v1.5.1-linux", b"km-v1.5.0-linux")]:
            with self.assertRaises(ValueError): a.checksum_rows(body, rows)

    def test_transport_rejects_redirect_encoding_and_overrun(self):
        _, _, _, _, url = fixture()
        class Response(io.BytesIO):
            status = 200
            headers = {}
            def geturl(self): return url
        class Opener:
            def __init__(self, response): self.response = response
            def open(self, *args, **kwargs): return self.response
        for encoded, limit in [(True, 3), (False, 2)]:
            response = Response(b"abc")
            response.headers = {"Content-Encoding": "gzip"} if encoded else {}
            with patch.object(a.urllib.request, "build_opener", return_value=Opener(response)):
                with self.assertRaises(ValueError): a.fetch(url, limit)
        with self.assertRaises(ValueError):
            a.NoRedirect().redirect_request(None, None, 302, "", {}, "https://evil.test/")

    def test_main_annotated_tag_downloads_and_lightweight_tag_fails_before_io(self):
        old = Path.cwd()
        with tempfile.TemporaryDirectory(prefix="km-assets-test-") as temp:
            os.chdir(temp)
            try:
                def git(*args):
                    return subprocess.check_output(["git", *args], text=True, stderr=subprocess.DEVNULL).strip()
                git("init", "-q"); git("config", "user.email", "test@example.org")
                git("config", "user.name", "Test"); git("commit", "--allow-empty", "-qm", "fixture")
                commit = git("rev-parse", "HEAD")
                blobs, _, raw, _, url = fixture(commit)
                git("tag", "-a", a.TAG, "-m", "KM-Release-Manifest: " + url)
                def fake_fetch(address, limit, destination=None):
                    body = raw if address == url else blobs[address.rsplit("/", 1)[1]]
                    self.assertLessEqual(len(body), limit)
                    if destination is not None: destination.write(body)
                    return len(body), hashlib.sha256(body).hexdigest(), body if destination is None else b""
                with patch.dict(os.environ, RELEASE_TAG=a.TAG), patch.object(a, "fetch", side_effect=fake_fetch):
                    with contextlib.redirect_stdout(io.StringIO()): a.main()
                    for name, body in blobs.items(): self.assertEqual((Path("release-assets") / name).read_bytes(), body)
                    # Existing local output is never replaced on a repeated invocation.
                    with self.assertRaises(FileExistsError): a.main()
                git("tag", "-d", a.TAG); git("tag", a.TAG)
                with patch.dict(os.environ, RELEASE_TAG=a.TAG), patch.object(a, "fetch") as fetch:
                    with self.assertRaises(ValueError): a.main()
                    fetch.assert_not_called()
            finally:
                os.chdir(old)


if __name__ == "__main__":
    unittest.main(verbosity=2)
