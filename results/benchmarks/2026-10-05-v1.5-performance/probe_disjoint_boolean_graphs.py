"""Exhaustive four-role Boolean disjointness controls with an independent oracle."""
import hashlib
import itertools
import json
import os
from pathlib import Path
import subprocess
import tree_watchdog as watchdog

root = Path(__file__).resolve().parent
binary = Path('/workspace/.work/target-integral-decimal/release/km')
work = Path('/tmp/agent/km-v150-diagnostics/disjoint-boolean-graphs-v1')
work.mkdir(exist_ok=False)
env = {k:v for k,v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_NATIVE_FULL='1', KM_HT_DDB='1', KM_EXPERIMENTAL_DATA_ROLE_DISJOINT='1',
           KM_THREADS='1', RAYON_NUM_THREADS='1', OMP_NUM_THREADS='1')
watchdog.protect_supervisor()
cpu = min(os.sched_getaffinity(0))
def child():
    watchdog.child_preexec()
    os.sched_setaffinity(0, {cpu})
def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
pairs = list(itertools.combinations(range(4), 2))
report = dict(diagnostic_only=True, release_approved=False, binary_sha256=digest(binary),
              runner_sha256=digest(Path(__file__)), timeout_s=5, memory_gib=20,
              oracle='Existential Boolean witnesses with disjoint role edges are exactly graph 2-colorings.',
              flags={k:v for k,v in env.items() if k.startswith('KM_')}, cases=[])
for mask in range(1 << len(pairs)):
    edges = [pair for bit,pair in enumerate(pairs) if mask & (1 << bit)]
    satisfiable = any(all(colors[a] != colors[b] for a,b in edges)
                      for colors in itertools.product([False,True], repeat=4))
    axioms = ['Prefix(:=<urn:disjoint:>) Ontology(Declaration(Class(:A))']
    for i in range(4):
        axioms += [f'Declaration(DataProperty(:r{i}))', f'DataPropertyRange(:r{i} xsd:boolean)']
    axioms += [f'DisjointDataProperties(:r{a} :r{b})' for a,b in edges]
    axioms += ['SubClassOf(:A ObjectIntersectionOf(' + ' '.join(
        f'DataSomeValuesFrom(:r{i} xsd:boolean)' for i in range(4)) + ')))']
    source = work / f'{mask}.ofn'; source.write_text('\n'.join(axioms)+'\n')
    output = work / f'{mask}.json'; stderr = work / f'{mask}.stderr'
    with output.open('w') as out, stderr.open('w') as err:
        proc = subprocess.Popen([str(binary), 'classify', '--route', 'ht_bridge', str(source)],
                                stdout=out, stderr=err, env=env, preexec_fn=child)
        run = watchdog.monitor(proc, timeout=5, memcap_bytes=20*1024**3)
    answer = json.loads(output.read_text()) if proc.returncode == 0 else None
    passed = (run.status == 'ok' and proc.returncode == 0 and answer['consistent'] is True
              and answer['dropped'] == 0 and (':A' not in answer['unsatisfiable']) == satisfiable)
    report['cases'].append(dict(mask=mask, edges=edges, expected_A_satisfiable=satisfiable,
        passed=passed, status=run.status, exit_code=proc.returncode, answer=answer,
        source_sha256=digest(source), output_sha256=digest(output), stderr_sha256=digest(stderr)))
report['passed'] = sum(c['passed'] for c in report['cases'])
(root / 'disjoint-boolean-graphs-v1-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(f"{report['passed']}/{len(report['cases'])} passed", flush=True)
