"""Small semantic controls for the isolated disjoint-role encoding."""
import json
import os
from pathlib import Path
import subprocess
import sys
from measure_classification import digest
import tree_watchdog as watchdog

binary = Path('/workspace/.work/target-integral-decimal/release/km')
root = Path(__file__).resolve().parent
work = Path('/tmp/agent/km-v150-diagnostics/data-disjoint-controls-v2')
work.mkdir(exist_ok=False)
watchdog.protect_supervisor()
env = {k:v for k,v in os.environ.items() if not k.startswith('KM_')}
env.update(KM_HT_NATIVE_FULL='1', KM_HT_DDB='1', KM_HT_ONLY='bridge', KM_NOMINALS='1',
           KM_THREADS='1', RAYON_NUM_THREADS='1', OMP_NUM_THREADS='1',
           KM_EXPERIMENTAL_DATA_ROLE_DISJOINT='1', KM_EXPERIMENTAL_DATA_PADDING='1',
           KM_HT_STATS='1', KM_BRIDGE_PROGRESS='1')
base = 'Prefix(:=<urn:disjoint:>) Ontology(Declaration(Class(:A)) Declaration(DataProperty(:r)) Declaration(DataProperty(:s)) DataPropertyRange(:r xsd:boolean) DataPropertyRange(:s xsd:boolean) DisjointDataProperties(:r :s) '
cases = [
 ('same_value', 'DataPropertyAssertion(:r :a "true"^^xsd:boolean) DataPropertyAssertion(:s :a "1"^^xsd:boolean)', False),
 ('different_values', 'DataPropertyAssertion(:r :a "true"^^xsd:boolean) DataPropertyAssertion(:s :a "false"^^xsd:boolean)', True),
 ('distinct_objects', 'DataPropertyAssertion(:r :a "true"^^xsd:boolean) DataPropertyAssertion(:s :b "true"^^xsd:boolean)', True),
 ('boolean_two_disjoint', 'ClassAssertion(ObjectIntersectionOf(DataSomeValuesFrom(:r xsd:boolean) DataSomeValuesFrom(:s xsd:boolean)) :a)', True),
 ('boolean_three_disjoint', 'Declaration(DataProperty(:t)) DataPropertyRange(:t xsd:boolean) DisjointDataProperties(:r :s :t) ClassAssertion(ObjectIntersectionOf(DataSomeValuesFrom(:r xsd:boolean) DataSomeValuesFrom(:s xsd:boolean) DataSomeValuesFrom(:t xsd:boolean)) :a)', False),
 ('shared_functional_super', 'Declaration(DataProperty(:t)) FunctionalDataProperty(:t) SubDataPropertyOf(:r :t) SubDataPropertyOf(:s :t) DataPropertyAssertion(:r :a "true"^^xsd:boolean) DataPropertyAssertion(:s :a "false"^^xsd:boolean)', False),
]
report = dict(diagnostic_only=True, binary_sha256=digest(binary), flags=env,
              release_approved=False, cases=[])
# Record only task-specific flags, never inherited environment credentials.
report['flags'] = {k:v for k,v in env.items() if k.startswith('KM_')}
cpu = min(os.sched_getaffinity(0))
def child():
    watchdog.child_preexec()
    os.sched_setaffinity(0, {cpu})
for name, axioms, expected in cases:
    query_case = name.startswith('boolean_')
    expected_unsat = name == 'boolean_three_disjoint'
    if query_case:
        axioms = axioms.replace('ClassAssertion(ObjectIntersectionOf(', 'SubClassOf(:A ObjectIntersectionOf(').replace(') :a)', '))')
        expected = True
    source = work / (name + '.ofn')
    source.write_text(base + axioms + ')')
    stdout = work / (name + '.json')
    stderr = work / (name + '.stderr')
    # The exact ground-source compiler is required for data assertions.
    with stdout.open('w') as out, stderr.open('w') as err:
        command = [str(binary), 'classify'] + (['--route', 'ht_bridge'] if query_case else []) + [str(source)]
        run_env = dict(env) if query_case else dict(env, KM_GROUND_RULE_SOURCE='1')
        proc = subprocess.Popen(command, stdout=out, stderr=err, env=run_env, preexec_fn=child)
        execution = watchdog.monitor(proc, timeout=5, memcap_bytes=20*1024**3)
    answer = json.loads(stdout.read_text()) if proc.returncode == 0 else None
    passed = execution.status == 'ok' and proc.returncode == 0 and answer['dropped'] == 0 and answer['consistent'] == expected
    if query_case and answer is not None:
        passed = passed and (('urn:disjoint:A' in answer['unsatisfiable']) == expected_unsat)
    report['cases'].append(dict(name=name, expected_A_unsatisfiable=expected_unsat if query_case else None, expected_consistent=expected, status=execution.status,
        exit_code=proc.returncode, passed=passed, answer=answer, source_sha256=digest(source),
        stderr=stderr.read_text()))
    (root / 'data-disjoint-control-v2-results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(name, passed, execution.status, proc.returncode, flush=True)
