"""Download prevalidated v1.5.3 assets bound by an annotated release tag.

This verifies transport identity, not certification or performance acceptance.
No credentials are required for the allowlisted public HTTPS downloads.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import urllib.request

TAG = "v1.5.3"
HEX = r"[0-9a-f]{64}"
COMMIT = r"[0-9a-f]{40}"
NAMES = {
    "km-v1.5.3-linux-x86_64": 256 << 20,
    "km-v1.5.3-certified-source.tar.gz": 256 << 20,
    "build-completion.json": 8 << 20,
    "BENCHMARKS.md": 16 << 20,
    "kobayashi-marust-protege-1.5.3.jar": 32 << 20,
    "SHA256SUMS": 64 << 10,
}
PREFIX = "https://leechuck.de/km-release-assets/v1.5.3/"
POINTER = re.compile(
    r"KM-Release-Manifest: (https://leechuck\.de/km-release-assets/v1\.5\.3/"
    r"(" + COMMIT + r")/(" + HEX + r")/manifest\.json)"
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def tag_pointer(tag_object, expected_commit):
    headers, message = tag_object.split("\n\n", 1)
    lines = headers.splitlines()
    require(lines[:3] == ["object " + expected_commit, "type commit", "tag " + TAG],
            "annotated tag must point directly at the checked-out release commit")
    candidates = [line for line in message.splitlines()
                  if line.startswith("KM-Release-Manifest")]
    require(len(candidates) == 1, "exactly one manifest pointer is required")
    match = POINTER.fullmatch(candidates[0])
    require(match is not None, "manifest pointer must use the exact allowlisted HTTPS path")
    require(match[2] == expected_commit, "manifest URL commit differs from checked-out commit")
    return match[1], match[3]


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key")
        result[key] = value
    return result


def manifest_rows(raw, expected_sha, expected_commit):
    require(len(raw) <= 64 << 10, "manifest exceeds 64 KiB")
    require(hashlib.sha256(raw).hexdigest() == expected_sha, "manifest SHA mismatch")
    doc = json.loads(raw, object_pairs_hook=no_duplicate_keys)
    require(set(doc) == {"schema", "tag", "commit", "assets"}, "unexpected manifest fields")
    require(doc["schema"] == "km-release-assets-v1" and doc["tag"] == TAG
            and doc["commit"] == expected_commit, "manifest release identity mismatch")
    require(type(doc["assets"]) is list and len(doc["assets"]) == len(NAMES),
            "manifest must contain exactly the six release assets")
    rows = {}
    for row in doc["assets"]:
        require(type(row) is dict and set(row) == {"name", "size", "sha256"},
                "unexpected asset fields")
        name = row["name"]
        require(type(name) is str and name in NAMES and name not in rows,
                "unlisted or duplicate asset name")
        require(type(row["size"]) is int and 0 < row["size"] <= NAMES[name],
                "invalid or excessive asset size")
        require(type(row["sha256"]) is str and re.fullmatch(HEX, row["sha256"]),
                "invalid asset SHA")
        rows[name] = row
    require(set(rows) == set(NAMES), "asset whitelist incomplete")
    return rows


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise ValueError("release asset redirects are forbidden")


def fetch(url, limit, destination=None):
    # Caller constructs every URL from the strictly parsed manifest path and
    # fixed filename whitelist. Never follow a redirect to a different origin.
    require(url.startswith(PREFIX), "download origin is not allowlisted")
    opener = urllib.request.build_opener(NoRedirect)
    request = urllib.request.Request(url, headers={"Accept-Encoding": "identity"})
    with opener.open(request, timeout=60) as response:
        require(response.status == 200 and response.geturl() == url, "unexpected HTTP response")
        require(response.headers.get("Content-Encoding", "identity") == "identity",
                "encoded response forbidden")
        digest = hashlib.sha256()
        count = 0
        chunks = []
        while True:
            chunk = response.read(1 << 20)
            if not chunk:
                break
            count += len(chunk)
            require(count <= limit, "download exceeds expected size")
            digest.update(chunk)
            if destination is None:
                chunks.append(chunk)
            else:
                destination.write(chunk)
    return count, digest.hexdigest(), b"".join(chunks)


def checksum_rows(raw, assets):
    expected = {name: row["sha256"] for name, row in assets.items() if name != "SHA256SUMS"}
    actual = {}
    for line in raw.decode("ascii").splitlines():
        match = re.fullmatch(r"(" + HEX + r")  ([A-Za-z0-9_.-]+)", line)
        require(match is not None and match[2] not in actual, "invalid checksum line")
        actual[match[2]] = match[1]
    require(actual == expected, "SHA256SUMS must list exactly the other five assets")


def main():
    require(os.environ.get("RELEASE_TAG") == TAG, "unexpected release tag")
    git = lambda *args: subprocess.check_output(["git", *args], text=True).strip()
    ref = "refs/tags/" + TAG
    require(git("cat-file", "-t", ref) == "tag", "lightweight release tags are forbidden")
    commit = git("rev-parse", "HEAD^{commit}")
    require(re.fullmatch(COMMIT, commit), "invalid checked-out commit")
    url, manifest_sha = tag_pointer(git("cat-file", "tag", ref), commit)
    _, _, raw = fetch(url, 64 << 10)
    rows = manifest_rows(raw, manifest_sha, commit)
    # The checkout starts clean. Never overwrite another attempt's downloads.
    out = Path("release-assets")
    out.mkdir(exist_ok=False)
    (out / "manifest.json").write_bytes(raw)
    for name in NAMES:
        row = rows[name]
        with (out / name).open("xb") as stream:
            size, sha, _ = fetch(url.rsplit("/", 1)[0] + "/" + name, row["size"], stream)
        require(size == row["size"] and sha == row["sha256"], "asset size or SHA mismatch: " + name)
    checksum_rows((out / "SHA256SUMS").read_bytes(), rows)
    print(json.dumps({"status": "verified_prevalidated_asset_bytes", "tag": TAG,
                      "commit": commit, "manifest_sha256": manifest_sha, "assets": rows}))


if __name__ == "__main__":
    main()
