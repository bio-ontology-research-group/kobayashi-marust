"""Bounded local diagnostic of an unpromoted datatype-disjointness candidate."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from measure_classification import digest, measure
from compare_taxonomies import compare
import tree_watchdog as watchdog

root = Path(__file__).resolve().parent
work = Path('/tmp/agent/km-v150-diagnostics/data-disjoint-14379')
source = Path('/tmp/agent/km-v150-diagnostics/timeout-profile-sources/ore_ont_14379.owl')
row = next(r for r in json.loads((root / 'full-candidate-inputs.json').read_text())['inputs']
           if r['ontology'] == 'ore_ont_14379')
assert digest(source) == row['sha256']
reference = work / 'reference'
assert digest(reference / 'audit.json') == row['reference_audit_sha256']
audit = json.loads((reference / 'audit.json').read_text())
assert audit['source_sha256'] == row['sha256']
target = Path('/workspace/.work/target-integral-decimal/release/km')
binary = work / ('km-data-disjoint-shadow-' + digest(target)[:12])
shutil.copy2(target, binary)
inventory = {'artifacts': [{'id': 'km', 'path': str(binary), 'sha256': digest(binary)}]}
report = dict(diagnostic_only=True, release_approved=False, input=row, artifact=inventory,
              scope='Unpromoted shadow with existing padding/decimal changes; 15-second local diagnostic only.',
              runner_sha256=digest(__file__), attempts=[])
watchdog.protect_supervisor()
for arm in ['off', 'on']:
    for key in list(os.environ):
        if key.startswith('KM_'):
            del os.environ[key]
    flags = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
                 KM_BRIDGE_SUBJECT_WORKERS_OVERRIDE='1', KM_TIMING='1',
                 KM_HT_STATS='1', KM_BRIDGE_PROGRESS='1', KM_EXPERIMENTAL_DATA_PADDING='1')
    if arm == 'on':
        flags['KM_EXPERIMENTAL_DATA_ROLE_DISJOINT'] = '1'
    os.environ.update(flags)
    output = work / arm
    record = measure(inventory, 'km', source, row['sha256'], output, timeout=15, memory_mib=20480)
    result = dict(arm=arm, flags=flags, record=record, comparisons={}, verified=False)
    if record['status'] == 'executed_unvalidated':
        command = [sys.executable, str(root / 'canonicalize.py'), '--input', str(output / 'taxonomy.raw'),
                   '--format', 'km-json', '--signature', str(reference / 'signature.tsv'),
                   '--output-prefix', str(output / 'canonical'),
                   '--fingerprint-script', str(root / 'full_iri_fingerprint.py')]
        with (output / 'audit.stdout').open('w') as stdout, (output / 'audit.stderr').open('w') as stderr:
            proc = subprocess.Popen(command, stdout=stdout, stderr=stderr, preexec_fn=watchdog.child_preexec)
            watched = watchdog.monitor(proc, timeout=60, memcap_bytes=20 * 1024**3)
        result['audit_execution'] = dict(status=watched.status, exit_code=proc.returncode)
        if watched.status == 'ok' and proc.returncode == 0:
            answer = json.loads((output / 'canonical.validated.json').read_text())
            for method in ['konclude', 'hermit', 'openllet', 'jfact']:
                previous = audit['outcomes'].get(method, {})
                if previous.get('status') != 'canonicalized_requires_comparison':
                    continue
                path = reference / (method + '.validated.json')
                assert digest(path) == previous['canonical_sha256']
                result['comparisons'][method] = compare(answer, json.loads(path.read_text()))
            result['verified'] = any(c.get('agreement') is True for c in result['comparisons'].values())
    result['stderr_sha256'] = digest(output / 'stderr')
    result['trace'] = (output / 'stderr').read_text().splitlines()
    report['attempts'].append(result)
    (root / 'data-disjoint-shadow-diagnostic.json').write_text(json.dumps(report, indent=2) + '\n')
    print(arm, record['status'], record.get('wall_s'), result['verified'], flush=True)
