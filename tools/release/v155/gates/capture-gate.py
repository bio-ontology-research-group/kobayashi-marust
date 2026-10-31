"""Run one Lean certification gate from the exact bound source and write a receipt.

Workstation edition of the v1.5.1-v1.5.4 capture-gate runner, v1.5.5: the
fifth gate `rules` (lean/run-rules-certification-gate.sh, native checkers
rules-inert-sort-release-check and rules-cert-check) and the hash-bound ORE
7278 input it needs (KM_RULES_GATE_ORE_7278). All pins come
from pins.json (written by prepare.py); the checks are the same: bound
source, bound tools, no pre-existing native checkers, no concurrent
compilers, free-space floors, no sorryAx, tamper-evident receipt.
"""
import argparse, datetime, hashlib, json, os, re, subprocess, time, signal, importlib.util, shutil
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--gate', choices=['cb', 'elc', 'ht', 'routing', 'rules'], required=True)
a = p.parse_args()
w = Path(__file__).resolve().parent
pins = json.loads((w / 'pins.json').read_text())
work = w / 'gate-work'
mf = w / 'complete-source-manifest.json'
snap = Path(pins['snapshot'])
mount = pins['repo_mount']
manifest = json.loads(mf.read_text())
gate = snap / 'lean' / ('run-' + a.gate + '-certification-gate.sh')
logs = work / 'logs'
logs.mkdir(parents=True, exist_ok=True)
log = logs / (a.gate + '-gate.log')
receipt = work / (a.gate + '-gate-receipt.json')
assert not receipt.exists(), receipt


def H(f):
    h = hashlib.sha256()
    with Path(f).open('rb') as stream:
        for b in iter(lambda: stream.read(1048576), b''):
            h.update(b)
    return h.hexdigest()


def verify(root):
    return [n for n, row in manifest['files'].items()
            if H(root / n) != row['sha256']
            or bool((root / n).stat().st_mode & 0o111) != (row['mode'] == '100755')
            or oct((root / n).stat().st_mode & 0o777) != row['actual_permissions']]


def capacity():
    return {x: shutil.disk_usage(x).free for x in [mount, '/tmp']}


def processes():
    rows = []
    for path in Path('/proc').glob('[0-9]*/comm'):
        try:
            comm = path.read_text().strip()
            if comm in ['cargo', 'rustc', 'lake', 'lean', 'km']:
                rows.append({'pid': int(path.parent.name), 'comm': comm})
        except (FileNotFoundError, ProcessLookupError):
            pass
    return rows


tool_binding = w / 'tool-bindings.json'
assert H(tool_binding) == pins['tool_bindings_sha256']
bound_tools = json.loads(tool_binding.read_text())
assert all(H(path) == value for path, value in bound_tools['files'].items())
assert H(gate) == bound_tools['gate_scripts'][a.gate]
assert H(mf) == pins['manifest_sha256']
assert manifest['git_commit'] == pins['commit']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=snap, text=True).strip() == manifest['git_commit']
assert not subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=snap, text=True).strip()
assert not verify(snap)
assert not processes(), processes()
before = capacity()
assert before['/tmp'] > 8 * 1024**3 and before[mount] > 20 * 1024**3, before
assert (snap / 'lean/.lake').is_dir() and not (snap / 'lean/.lake').is_symlink()
names = re.findall(r'^name = "([^"]+)"', (snap / 'lean/lakefile.toml').read_text(), re.M)
if a.gate in ['cb', 'ht']:
    selected = [n for n in names if n.startswith(a.gate + '-')]
else:
    selected = {'elc': ['elc-cert-check'], 'routing': ['km-automatic-routing-check'],
                'rules': ['rules-inert-sort-release-check', 'rules-cert-check']}[a.gate]
binroot = snap / 'lean/.lake/build/bin'
assert all(not (binroot / n).exists() for n in selected), 'preexisting native checker bypass prohibited'
home = str(Path.home())
env = {k: v for k, v in os.environ.items()
       if not k.startswith(('KM_', 'CARGO_', 'GIT_', 'LEAN_', 'RUST', 'LLVM_PROFILE')) and k not in ['LD_PRELOAD', 'LD_LIBRARY_PATH']}
cpuset = os.environ.get('KM_CERT_CPUSET', '44-51')
env.update(PATH=str(w / 'control-bin') + ':' + home + '/.cargo/bin:' + home + '/.elan/bin:' + env.get('PATH', ''),
           CARGO_HOME=home + '/.cargo', RUSTUP_HOME=home + '/.rustup', ELAN_HOME=home + '/.elan',
           CARGO_BUILD_JOBS='4', CARGO_INCREMENTAL='0', CARGO_NET_OFFLINE='true', RUST_TEST_THREADS='1',
           RUSTUP_TOOLCHAIN='stable', KM_WORK_ROOT=str(work), KM_CERT_LEAN_THREADS=os.environ.get('KM_CERT_LEAN_THREADS', '8'),
           KM_CERT_LEAN_CPUSET=cpuset, KM_CERT_KEEP_NATIVE_CHECKERS='1')
if a.gate == 'rules':
    assert H(pins['rules_gate_ore_7278']) == pins['rules_gate_ore_7278_sha256']
    env['KM_RULES_GATE_ORE_7278'] = pins['rules_gate_ore_7278']
helper = Path(pins['helper'])
assert H(helper) == pins['helper_sha256']
spec = importlib.util.spec_from_file_location('bound_subreaper', helper)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
command = ['taskset', '-c', cpuset, 'bash', str(gate)]
r = {'status': 'running', 'purpose': 'v' + pins['version'].replace('.', '') + '_release_exact_source_lean_gate', 'gate': a.gate, 'runner_sha256': H(__file__),
     'tool_binding_sha256': H(tool_binding), 'source_manifest': str(mf), 'source_manifest_sha256': H(mf),
     'git_commit': manifest['git_commit'], 'source_snapshot_policy': manifest['snapshot_policy'], 'execution_source': str(snap),
     'source_files': len(manifest['files']), 'source_bytes_modes_verified_before': True,
     'source_freshness': 'No mtime forcing; exact same live source path reuses current semantic cache. All selected native executables absent before actual rebuild.',
     'script_sha256': H(gate), 'command': command,
     'environment': {k: env[k] for k in ['CARGO_HOME', 'RUSTUP_HOME', 'ELAN_HOME', 'CARGO_BUILD_JOBS', 'CARGO_INCREMENTAL', 'KM_WORK_ROOT', 'KM_CERT_LEAN_THREADS', 'KM_CERT_LEAN_CPUSET', 'KM_CERT_KEEP_NATIVE_CHECKERS'] + (['KM_RULES_GATE_ORE_7278'] if a.gate == 'rules' else [])},
     'selected_native_checkers': selected, 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'log': str(log),
     'capacity_before': before, 'runtime_floor_bytes': {'/tmp': 2 * 1024**3, mount: 10 * 1024**3},
     'entry_exit_floor_bytes': {'/tmp': 8 * 1024**3, mount: 20 * 1024**3}, 'cleanup_helper_sha256': H(helper)}
receipt.write_text(json.dumps(r, indent=2) + '\n')
start = time.monotonic()
mins = before.copy()
breach = None
scope = mod.SubreaperScope().begin()
with log.open('wb') as stdout:
    proc = subprocess.Popen(command, cwd=snap, env=env, stdout=stdout, stderr=subprocess.STDOUT, start_new_session=True)
    scope.register_root(proc.pid)
    r['actual_pid'] = proc.pid
    receipt.write_text(json.dumps(r, indent=2) + '\n')
    print(json.dumps({'gate': a.gate, 'actual_pid': proc.pid, 'status': 'running'}), flush=True)
    while proc.poll() is None:
        free = capacity()
        mins = {key: min(mins[key], free[key]) for key in mins}
        if free['/tmp'] <= 2 * 1024**3 or free[mount] <= 10 * 1024**3:
            breach = free
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
            break
        time.sleep(1)
    code = proc.wait()
cleanup = scope.finish()
r.update(actual_exit_code=code, exit_code=code, status='passed' if code == 0 else 'failed',
         ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), wall_s=time.monotonic() - start, log_sha256=H(log),
         minimum_free_bytes_observed=mins, runtime_floor_breach=breach, child_tree_cleanup=cleanup)
text = log.read_text(errors='replace')
r['test_results'] = re.findall(r'^test result: .+$', text, re.M)
r['ignored_test_lines'] = re.findall(r'^test .*\.\.\. ignored.*$', text, re.M)
r['sorryAx_occurrences_in_gate_log'] = text.count('sorryAx')
r['surface_log'] = str(work / 'artifacts' / (a.gate + '-certification-surface.log'))
surface = Path(r['surface_log'])
surface_text = surface.read_text(errors='replace') if surface.is_file() else ''
r['surface_log_sha256'] = H(surface) if surface.is_file() else None
r['surface_log_exists_nonempty'] = bool(surface_text.strip())
r['surface_sorryAx_occurrences'] = surface_text.count('sorryAx')
r['axiom_audit_lines'] = [x for x in surface_text.splitlines() if 'axiom' in x]
r['checker_bindings_after'] = []
for name in selected:
    f = binroot / name
    if f.exists():
        r['checker_bindings_after'].append({'name': name, 'sha256': H(f), 'bytes': f.stat().st_size, 'executable': os.access(f, os.X_OK),
                                            'mtime_ns': f.stat().st_mtime_ns,
                                            'lake_hash': (binroot / (name + '.hash')).read_text().strip() if (binroot / (name + '.hash')).exists() else None})
        f.unlink()
r['all_native_checkers_generated_and_hashbound'] = len(r['checker_bindings_after']) == len(selected) and all(x['bytes'] > 0 and x['executable'] for x in r['checker_bindings_after'])
r['all_native_checkers_removed_after_audit'] = all(not (binroot / n).exists() for n in selected)
r['live_source_changes_after'] = verify(snap)
r['git_commit_after'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=snap, text=True).strip()
r['tracked_changes_after'] = subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=snap, text=True).splitlines()
r['capacity_after'] = capacity()
r['entry_exit_floor_passed'] = r['capacity_after']['/tmp'] > 8 * 1024**3 and r['capacity_after'][mount] > 20 * 1024**3
r['tool_changes_after'] = [path for path, value in bound_tools['files'].items() if H(path) != value]
r['active_compilers_after'] = processes()
r['required_evidence_present'] = r['surface_log_exists_nonempty'] and bool(r['axiom_audit_lines']) and r['all_native_checkers_generated_and_hashbound'] and bool(r['test_results'])
r['counts'] = {key: sum(int(x) for x in re.findall(r'(\d+) ' + key, '\n'.join(r['test_results']))) for key in ['passed', 'failed', 'ignored']}
r['counts']['groups'] = len(r['test_results'])
if (breach or r['tool_changes_after'] or r['live_source_changes_after'] or r['tracked_changes_after']
        or r['git_commit_after'] != manifest['git_commit'] or r['surface_sorryAx_occurrences'] or r['sorryAx_occurrences_in_gate_log']
        or not r['required_evidence_present'] or not r['entry_exit_floor_passed'] or r['active_compilers_after']
        or cleanup.get('status') != 'confirmed_empty_after_cleanup' or cleanup.get('remaining_processes') != []
        or cleanup.get('subreaper_restored') is not True):
    r['status'] = 'rejected'
receipt.write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps({'gate': a.gate, 'status': r['status'], 'actual_exit_code': code, 'counts': r['counts'], 'capacity_after': r['capacity_after'],
                  'runtime_floor_breach': breach, 'receipt_sha256': H(receipt)}, indent=2), flush=True)
raise SystemExit(0 if r['status'] == 'passed' else 1)
