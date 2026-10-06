"""Build the pinned candidate with Cargo's production LTO/codegen settings."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

root = Path('results/benchmarks/2026-10-05-v1.5-performance')
tmp = Path('/tmp/agent/km-v150-diagnostics')
manifest = root / 'graph-json-source-manifest.json'
files = json.loads(manifest.read_text())['files']
def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def check():
    assert all(digest(path) == sha for path, sha in files.items())
check()
env = dict(os.environ, PATH='/state/cargo/bin:' + os.environ['PATH'],
    CARGO_HOME='/state/cargo', RUSTUP_HOME='/state/rustup',
    CARGO_TARGET_DIR=str(Path('.work/target-local').resolve()),
    CARGO_PROFILE_RELEASE_LTO='true', CARGO_PROFILE_RELEASE_CODEGEN_UNITS='1',
    CARGO_INCREMENTAL='0')
command = ['cargo', 'build', '--release', '--locked', '--manifest-path', 'engine/Cargo.toml', '--bin', 'km', '-v']
log = tmp / 'graph-json-production-build.log'
with log.open('w') as out:
    result = subprocess.run(command, env=env, stdout=out, stderr=subprocess.STDOUT)
check()
receipt = dict(command=command, source_manifest_sha256=digest(manifest),
    runner_sha256=digest(__file__), exit_code=result.returncode,
    source_files_rechecked=len(files), build_log_sha256=digest(log),
    production_profile=True, profile=dict(lto=True, codegen_units=1, incremental=False),
    release_approved=False)
if result.returncode == 0:
    binary = Path(env['CARGO_TARGET_DIR']) / 'release/km'
    pinned = tmp / ('km-graph-json-production-' + digest(binary)[:12])
    shutil.copy2(binary, pinned)
    receipt.update(binary_sha256=digest(pinned), local_binary=str(pinned),
        rustc_version=subprocess.check_output(['rustc', '-Vv'],env=env,text=True))
(root / 'graph-json-production-build.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2), flush=True)
assert result.returncode == 0
