from pathlib import Path
import datetime, hashlib, importlib.util, json, os, re, shutil, signal, subprocess, time

# Workstation edition for v1.5.5 (from the v1.5.4 control): every pin comes from
# pins.json (prepare.py); all five Lean gate receipts (rules added) must have passed.
W = Path(__file__).resolve().parent
PINS = json.loads((W / 'pins.json').read_text())
S = Path(PINS['snapshot'])
MOUNT = PINS['repo_mount']
M = W / 'complete-source-manifest.json'
TOOLS = W / 'tool-bindings.json'
TARGET = W / 'gate-work/target'
OUT = W / 'full-rust-execution'
HELPER = Path(PINS['helper'])
HELPER_SHA = PINS['helper_sha256']
COMMIT = PINS['commit']
MF_SHA = PINS['manifest_sha256']
TOOL_SHA = PINS['tool_bindings_sha256']
CI_SHA = PINS['ci_sha256']
HOME = str(Path.home())
CPUSET = os.environ.get('KM_CERT_CPUSET', '36-43')

def H(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def J(path):
    return json.loads(Path(path).read_text())

def free():
    return {p: shutil.disk_usage(p).free for p in [MOUNT, '/tmp']}

def entry_guard():
    n = free()
    assert n[MOUNT] > 20 * 1024**3 and n['/tmp'] > 8 * 1024**3, n
    return n

def processes():
    out = []
    for p in Path('/proc').glob('[0-9]*/comm'):
        try:
            c = p.read_text().strip()
            if c in ['cargo', 'rustc', 'lake', 'lean', 'km']:
                out.append({'pid': int(p.parent.name), 'comm': c})
        except (FileNotFoundError, ProcessLookupError):
            pass
    return out

assert H(M) == MF_SHA and H(TOOLS) == TOOL_SHA and H(HELPER) == HELPER_SHA
manifest = J(M)
tools = J(TOOLS)
def verify():
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=S, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'diff', '--name-only', 'HEAD'], cwd=S, text=True).strip()
    assert not [n for n, row in manifest['files'].items() if H(S/n) != row['sha256'] or oct((S/n).stat().st_mode & 0o777) != row['actual_permissions'] or bool((S/n).stat().st_mode & 0o111) != (row['mode']=='100755')]
    assert all(H(p) == h for p, h in tools['files'].items())

verify()
assert not processes(), processes()
entry_guard()
ci = S/'.github/workflows/ci.yml'
assert H(ci) == CI_SHA
skips = re.search(r'checker_tests=\((.*?)\n\s*\)', ci.read_text(), re.S).group(1).split()
excluded = ['cb_live_state', 'elc_certificate', 'ht_taxonomy_certificate']
r_skips = len(skips)
gate_pins={}
for name in ['cb','elc','ht','routing','rules']:
    p=W/'gate-work'/(name+'-gate-receipt.json');gate=J(p)
    assert gate['status']=='passed' and gate['actual_exit_code']==0 and gate['source_manifest_sha256']==MF_SHA and gate['git_commit']==COMMIT
    assert gate['entry_exit_floor_passed'] and not gate['runtime_floor_breach'] and not gate['live_source_changes_after'] and not gate['tracked_changes_after'] and gate['git_commit_after']==COMMIT
    assert gate['surface_sorryAx_occurrences']==0 and gate['sorryAx_occurrences_in_gate_log']==0 and gate['all_native_checkers_generated_and_hashbound'] and gate['all_native_checkers_removed_after_audit']
    gate_pins[name]={'path':str(p),'sha256':H(p),'counts':gate['counts']}
coverage={'status':'covered_by_actual_current_exact_source_five_lean_gates','skipped_library_tests':skips,'excluded_integration_targets':excluded,'prior_9476_certificate_not_reused':True,'gate_receipts':gate_pins}
targets = sorted(p.stem for p in (S/'engine/tests').glob('*.rs') if p.stem not in excluded)
commands = [['cargo', 'test', '--release', '--jobs', '4', '--lib', '--', '--test-threads=1'] + sum((['--skip', n] for n in skips), [])]
commands += [['cargo', 'test', '--release', '--jobs', '4', '--test', n, '--', '--test-threads=1'] for n in targets]
worker_names = ['ofn', 'elc', 'kobayashi-marust', 'tableau_cli']
worker_command = ['cargo', 'build', '--release', '--jobs', '4'] + sum((['--bin', n] for n in worker_names), [])
env = {k:v for k,v in os.environ.items() if not k.startswith(('KM_', 'CARGO_', 'GIT_', 'LEAN_', 'RUST', 'LLVM_PROFILE')) and k not in ['LD_PRELOAD', 'LD_LIBRARY_PATH']}
env.update(PATH=str(W/'control-bin')+':'+HOME+'/.cargo/bin:'+HOME+'/.elan/bin:'+env.get('PATH', ''), CARGO_HOME=HOME+'/.cargo', RUSTUP_HOME=HOME+'/.rustup', ELAN_HOME=HOME+'/.elan', RUSTUP_TOOLCHAIN='stable', CARGO_BUILD_JOBS='4', CARGO_INCREMENTAL='0', CARGO_TARGET_DIR=str(TARGET))
spec = importlib.util.spec_from_file_location('bound_full_rust_subreaper', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
OUT.mkdir(exist_ok=False)
receipt_path = OUT/'receipt.json'
r = {'status': 'running', 'purpose': 'v'+PINS['version'].replace('.','')+'_ordinary_ci_rust_with_actual_current_exact_source_lean_coverage', 'base_git_commit': COMMIT, 'source_status':'exact_committed_clean_source', 'source_manifest_sha256': MF_SHA, 'source_files': len(manifest['files']), 'tool_binding_sha256': TOOL_SHA, 'ci_recipe_sha256': CI_SHA, 'current_exact_source_lean_coverage':'actual_all5_passed', 'driver_sha256': H(__file__), 'cleanup_helper_sha256': HELPER_SHA, 'checker_skip_actual_coverage': coverage, 'worker_build_command': worker_command, 'commands': commands, 'integration_targets': targets, 'attempts': [], 'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
start = time.monotonic()
def save():
    receipt_path.write_text(json.dumps(r, indent=2)+'\n')

def run(cmd, label, overrides=None):
    verify()
    assert not processes(), processes()
    row = {'command': ['taskset', '-c', CPUSET]+cmd, 'cwd': str(S/'engine'), 'log': str(OUT/(label+'.log')), 'free_bytes_before': entry_guard(), 'worker_overrides': overrides or {}, 'status': 'running'}
    r['attempts'].append(row)
    save()
    scope = helper.SubreaperScope().begin()
    t = time.monotonic()
    minimum = row['free_bytes_before'].copy()
    breach = None
    with Path(row['log']).open('wb') as f:
        p = subprocess.Popen(row['command'], cwd=S/'engine', env={**env, **(overrides or {})}, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        scope.register_root(p.pid)
        row['actual_pid'] = p.pid
        save()
        print(json.dumps({'status':'running', 'label':label, 'actual_pid':p.pid}), flush=True)
        while p.poll() is None:
            capacity = free()
            minimum = {k:min(minimum[k], capacity[k]) for k in minimum}
            if capacity[MOUNT] <= 10*1024**3 or capacity['/tmp'] <= 2*1024**3:
                breach = capacity
                try: os.killpg(p.pid, signal.SIGTERM)
                except ProcessLookupError: pass
                try: p.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    try: os.killpg(p.pid, signal.SIGKILL)
                    except ProcessLookupError: pass
                    p.wait()
                break
            time.sleep(1)
        code = p.wait()
    cleanup = scope.finish()
    text = Path(row['log']).read_text(errors='replace')
    counts = [tuple(map(int, x)) for x in re.findall(r'test result: .*? (\d+) passed; (\d+) failed; (\d+) ignored;', text)]
    row.update(exit_code=code, wall_s=time.monotonic()-t, log_sha256=H(row['log']), test_results=re.findall(r'^test result: .+$',text,re.M), counts={'groups':len(counts), 'passed':sum(x[0] for x in counts), 'failed':sum(x[1] for x in counts), 'ignored':sum(x[2] for x in counts)}, ignored_names=re.findall(r'^test (.+) \.\.\. ignored.*$',text,re.M), minimum_free_bytes_observed=minimum, runtime_floor_breach=breach, child_tree_cleanup=cleanup, status='passed' if code==0 else 'failed')
    save()
    assert code == 0 and not breach and cleanup['status'] == 'confirmed_empty_after_cleanup' and cleanup['remaining_processes'] == [] and cleanup['subreaper_restored'] is True, row
    verify()
    row['free_bytes_after'] = entry_guard()
    assert not processes(), processes()
    if label != 'workers':
        assert row['test_results'] and not row['counts']['failed'], row
    save()
    print(json.dumps({'status':'passed', 'label':label, 'counts':row['counts']}), flush=True)

save()
try:
    run(worker_command, 'workers')
    workers = {n:{'path':str(TARGET/'release'/n), 'sha256':H(TARGET/'release'/n)} for n in worker_names}
    r['workers'] = workers
    worker_overrides = {key:workers[n]['path'] for key,n in {'KM_OFN_BIN':'ofn','KM_ELC_BIN':'elc','KM_ENGINE':'kobayashi-marust','KM_TAB_BIN':'tableau_cli'}.items()}
    for i, cmd in enumerate(commands):
        run(cmd, '%02d-%s'%(i, 'lib' if i==0 else targets[i-1]), worker_overrides if i==0 else None)
        assert all(H(row['path']) == row['sha256'] for row in workers.values()), 'worker bytes changed'
    verify()
    r['source_bytes_modes_base_commit_tools_unchanged_after'] = True
    r['workers_unchanged_after'] = True
    r['free_bytes_after'] = entry_guard()
    r['active_compilers_after'] = processes()
    assert not r['active_compilers_after']
    r['status'] = 'passed_ordinary_rust_ci_current_lean_covered'
except BaseException as error:
    r['status'] = 'failed'
    r['error'] = repr(error)
    raise
finally:
    r.update(wall_s=time.monotonic()-start, ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), counts={k:sum(row['counts'][k] for row in r['attempts'] if 'counts' in row) for k in ['groups','passed','failed','ignored']}, completed_cargo_test_commands=sum(1 for row in r['attempts'] if row['command'][3:5]==['cargo','test'] and row['status']=='passed'))
    save()
print(json.dumps({'status':r['status'], 'counts':r['counts'], 'completed_cargo_test_commands':r['completed_cargo_test_commands'], 'receipt_sha256':H(receipt_path)}), flush=True)
