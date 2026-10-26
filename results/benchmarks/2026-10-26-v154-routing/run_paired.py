"""Paired routing-policy measurement on one half of the frozen ORE 2015 pool.

Every input runs twice on the same node with the same binary: once with
KM_ROUTING_POLICY=v153 and once under the general policy. The measurement and
audit protocol is the v1.5.3 release protocol (one core, 240 s, 20 GiB, scoped
watchdog, comparison with the pinned Konclude/HermiT/Openllet/JFact answers);
its modules are imported unchanged from the v1.5.3 run directory.
"""
import json
import os
from pathlib import Path
import subprocess
import sys

V153 = Path('/ibex/scratch/projects/c2014/hohndor/km/v150-performance-20261005/recovery-v153-scoped-20261025')
sys.path.insert(0, str(V153))
from compare_taxonomies import compare  # noqa: E402
from measure_classification import digest, measure  # noqa: E402
import tree_watchdog as watchdog  # noqa: E402
from scoped_snapshot import ScopedSnapshot  # noqa: E402

root = Path(__file__).resolve().parent
half = os.environ['KM_HALF']                      # 'design' or 'held_out'
policies = os.environ.get('KM_POLICIES', 'v153,general').split(',')
task = int(os.environ['SLURM_ARRAY_TASK_ID'])
tasks = int(os.environ['KM_TASKS'])
manifest = json.loads((V153 / 'full-candidate-inputs.json').read_text())
chosen = set(json.loads((root / 'split.json').read_text())[half])
rows = [r for r in manifest['inputs'] if r['ontology'] in chosen]
rows = rows[task::tasks]
inventory = json.loads((root / 'inventory.json').read_text())
os.environ.update(inventory['flags'])
os.environ['KM_TIMING'] = '1'
destination = root / ('paired-' + half + '-' + os.environ['SLURM_ARRAY_JOB_ID'])
summary_path = destination / 'chunks' / (str(task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', half=half, policies=policies, outcomes=[],
               inventory_sha256=digest(root / 'inventory.json'), runner_sha256=digest(__file__))


def publish():
    tmp = summary_path.with_suffix('.part')
    tmp.write_text(json.dumps(summary, indent=2) + '\n')
    tmp.replace(summary_path)


def audit(row, output, result):
    reference = Path(row['reference_directory'])
    assert digest(reference / 'audit.json') == row['reference_audit_sha256']
    ref = json.loads((reference / 'audit.json').read_text())
    prefix = output / 'canonical'
    command = [sys.executable, str(V153 / 'canonicalize.py'), '--input', str(output / 'taxonomy.raw'),
               '--format', 'km-json', '--signature', str(reference / 'signature.tsv'),
               '--output-prefix', str(prefix), '--fingerprint-script', str(V153 / 'full_iri_fingerprint.py')]
    with (output / 'audit.stdout').open('wb') as out, (output / 'audit.stderr').open('wb') as err:
        proc = subprocess.Popen(command, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                preexec_fn=watchdog.child_preexec)
        execution = watchdog.monitor(proc, timeout=600, memcap_bytes=20480 * 1024**2,
                                     snapshotter=ScopedSnapshot(proc.pid))
    assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
    answer = json.loads((output / 'canonical.validated.json').read_text())
    for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
        prior = ref['outcomes'].get(baseline, {})
        if prior.get('status') != 'canonicalized_requires_comparison':
            continue
        path = reference / (baseline + '.validated.json')
        assert digest(path) == prior['canonical_sha256']
        result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
    result['verified_solved'] = any(x.get('agreement') is True for x in result['comparisons'].values())
    result['wrong'] = any(x.get('agreement') is False for x in result['comparisons'].values()) and not result['verified_solved']


def route_trace(output):
    for name in ('stderr', 'stderr.txt', 'worker.stderr'):
        p = output / name
        if p.exists():
            return [l for l in p.read_text(errors='replace').splitlines()
                    if 'route=' in l or 'declined' in l or 'accepted' in l][:6]
    return []


publish()
watchdog.protect_supervisor()
for row in rows:
    for policy in policies:
        os.environ['KM_ROUTING_POLICY'] = policy
        output = destination / row['ontology'] / policy
        record = measure(inventory, 'km', row['path'], row['sha256'], output, timeout=240, memory_mib=20480)
        result = dict(ontology=row['ontology'], policy=policy, measurement_status=record['status'],
                      wall_s=record.get('wall_s'), peak_bytes=record.get('peak_bytes'),
                      verified_solved=False, wrong=False, comparisons={})
        if record['status'] == 'executed_unvalidated':
            try:
                audit(row, output, result)
            except Exception as error:
                result.update(audit_status='audit_error', error=str(error))
        result['route_trace'] = route_trace(output)
        summary['outcomes'].append(result)
        publish()
summary['status'] = 'complete'
publish()
