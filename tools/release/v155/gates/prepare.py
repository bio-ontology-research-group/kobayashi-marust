"""Bind the exact v1.5.5 gate source and tools (workstation edition).

usage: prepare.py <snapshot-clone> <expected-commit> <ctl-dir> [version]
Writes complete-source-manifest.json, tool-bindings.json and pins.json into
<ctl-dir> (the copy of tools/release/v155/gates used for this release). The
snapshot clone must be clean and checked out at the commit. v1.5.5 changes
against the v1.5.4 control: five gates (rules added), the ORE 7278 input the
rules gate needs is bound by hash, the ctl dir and version are arguments.
"""
from pathlib import Path
import hashlib, json, subprocess, sys

L = Path(sys.argv[1]).resolve()
COMMIT = sys.argv[2]
W = Path(sys.argv[3]).resolve()
VERSION = sys.argv[4] if len(sys.argv) > 4 else '1.5.5'
ORE_7278 = Path('/mnt/data2/workspaces/leechuck/software/kobayashi-marust/v150-corpus/files/ore_ont_7278.owl')
ORE_7278_SHA = '266688eca16aa5946aecca0be32cbff77d4339551dfcee5c6f55449b082221a5'  # full-candidate-inputs-ws.json
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=L, text=True).strip()
assert head == COMMIT, f"{head} != {COMMIT}"
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=L, text=True).strip()
records = [r for r in subprocess.check_output(['git', 'ls-tree', '-r', '-z', 'HEAD'], cwd=L, text=True).split('\0') if r]
tree = {r.split('\t')[1]: r.split('\t')[0].split() for r in records}
files = {}
for n, (mode, kind, oid) in sorted(tree.items()):
    if kind != 'blob':
        continue
    p = L / n
    if p.is_symlink() or not p.is_file():
        continue
    body = p.read_bytes()
    files[n] = {'sha256': hashlib.sha256(body).hexdigest(), 'mode': mode,
                'actual_permissions': oct(p.stat().st_mode & 0o777)}
m = {'schema': 'km-exact-commit-gate-source-v2', 'git_commit': head, 'execution_source': str(L),
     'snapshot_policy': 'Independent local clone checked out detached at the commit; every tracked regular file Git blob SHA256, Git mode and actual permission bound and verified before and after every gate.',
     'version': VERSION, 'files': files}
(W / 'complete-source-manifest.json').write_text(json.dumps(m, indent=2) + '\n')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert H(ORE_7278) == ORE_7278_SHA, 'ore_ont_7278.owl differs from the pinned corpus file'
home = Path.home()
tool_paths = [str(home / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),
              str(home / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo'),
              str(home / '.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'),
              str(home / '.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake'),
              str(W / 'control-bin/cargo')]
assert H(W / 'control-bin/cargo') == 'bd4f5883d4de280a8e33a7b2f67f6e10679148d2b9c306c72d80b14a38b22426', 'control-bin/cargo differs from the v1.5.4 control'
tools = {'schema': 'km-gate-tool-binding-v1', 'files': {p: H(p) for p in tool_paths},
         'gate_scripts': {g: H(L / 'lean' / f'run-{g}-certification-gate.sh') for g in ['cb', 'elc', 'ht', 'routing', 'rules']}}
(W / 'tool-bindings.json').write_text(json.dumps(tools, indent=2) + '\n')
helper = Path('/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/worktrees/v1.5.1/results/benchmarks/2026-10-14-v1.5.1-incremental/release-preparation/final-runtime-staging-v2-digest/cli-runtime-supplement-v2/runtime/timing-runner/process_tree_subreaper_v3.py')
pins = {'commit': head, 'snapshot': str(L), 'manifest_sha256': H(W / 'complete-source-manifest.json'),
        'tool_bindings_sha256': H(W / 'tool-bindings.json'), 'ci_sha256': H(L / '.github/workflows/ci.yml'),
        'helper': str(helper), 'helper_sha256': H(helper), 'repo_mount': '/mnt/data2', 'version': VERSION,
        'rules_gate_ore_7278': str(ORE_7278), 'rules_gate_ore_7278_sha256': ORE_7278_SHA}
(W / 'pins.json').write_text(json.dumps(pins, indent=2) + '\n')
print(json.dumps({k: pins[k] for k in ['commit', 'manifest_sha256', 'tool_bindings_sha256', 'ci_sha256']}, indent=1), len(files), 'files')
