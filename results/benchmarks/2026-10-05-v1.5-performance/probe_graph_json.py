"""Paired graph-output diagnostic using one binary and unchanged measurement/audit limits."""
import json
import os
from pathlib import Path
import subprocess
import sys

from compare_taxonomies import compare
from measure_classification import digest, measure
import tree_watchdog as watchdog


root = Path(__file__).resolve().parent
task = int(os.environ['SLURM_ARRAY_TASK_ID'])
manifest_path = root / 'full-candidate-inputs.json'
manifest = json.loads(manifest_path.read_text())
inventory_path = root / 'graph-json-artifact.json'
inventory = json.loads(inventory_path.read_text())
flags = dict(inventory['flags'])
assert len(manifest['inputs']) == 1920
cases = ['ore_ont_10689', 'ore_ont_8737', 'ore_ont_10174']
assert 0 <= task < 6
repetition = task % 2
row = next(r for r in manifest['inputs'] if r['ontology'] == cases[task // 2])
rows = [row, row]
arms = ['expanded', 'graph'] if repetition == 0 else ['graph', 'expanded']
destination = root / ('graph-json-probe-' + os.environ['SLURM_ARRAY_JOB_ID'])
summary_path = destination / 'chunks' / (str(task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', manifest_sha256=digest(manifest_path),
               inventory_sha256=digest(inventory_path), runner_sha256=digest(__file__),
               flags=flags, repetition=repetition, diagnostic_only=True, release_approved=False, outcomes=[])


def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)


publish()
watchdog.protect_supervisor()
for arm, row in zip(arms, rows):
    for key in list(os.environ):
        if key.startswith('KM_'):
            del os.environ[key]
    os.environ.update(flags)
    os.environ['KM_JSON_GRAPH_EDGES'] = '1' if arm == 'graph' else '0'
    output = destination / row['ontology'] / str(repetition) / arm
    record = measure(inventory, 'km', row['path'], row['sha256'], output,
                     timeout=240, memory_mib=20480)
    result = dict(arm=arm, repetition=repetition, graph_edges=arm == 'graph', ontology=row['ontology'], input_admission=row['input_admission'],
                  measurement_status=record['status'], wall_s=record.get('wall_s'),
                  peak_bytes=record.get('peak_bytes'), verified_solved=False,
                  comparisons={}, measurement_sha256=digest(output / 'record.json'))
    result['taxonomy_bytes'] = (output / 'taxonomy.raw').stat().st_size if (output / 'taxonomy.raw').exists() else None
    if record['status'] == 'executed_unvalidated' and row['input_admission'] == 'checks_passed':
        try:
            reference = Path(row['reference_directory'])
            assert digest(reference / 'audit.json') == row['reference_audit_sha256']
            audit = json.loads((reference / 'audit.json').read_text())
            assert audit['source_sha256'] == row['sha256']
            prefix = output / 'canonical'
            command = [sys.executable, str(root / 'canonicalize.py'),
                       '--input', str(output / 'taxonomy.raw'), '--format', 'km-json',
                       '--signature', str(reference / 'signature.tsv'),
                       '--output-prefix', str(prefix),
                       '--fingerprint-script', str(root / 'full_iri_fingerprint.py')]
            with (output / 'audit.stdout').open('wb') as out, (output / 'audit.stderr').open('wb') as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err,
                                        stdin=subprocess.DEVNULL, preexec_fn=watchdog.child_preexec)
                execution = watchdog.monitor(proc, timeout=600, memcap_bytes=20480 * 1024**2)
            result['audit_execution'] = dict(status=execution.status, exit_code=proc.returncode,
                                             wall_s=execution.wall_s, peak_bytes=execution.peak_bytes,
                                             timeout_s=600, memory_mib=20480)
            assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
            result['canonical_sha256'] = digest(output / 'canonical.validated.json')
            answer = json.loads((output / 'canonical.validated.json').read_text())
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                prior = audit['outcomes'].get(baseline, {})
                if prior.get('status') != 'canonicalized_requires_comparison':
                    continue
                path = reference / (baseline + '.validated.json')
                assert digest(path) == prior['canonical_sha256']
                result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
            result['verified_solved'] = any(x.get('agreement') is True
                                           for x in result['comparisons'].values())
            result['audit_status'] = 'compared'
        except Exception as error:
            result.update(audit_status='audit_error', error=str(error))
    elif record['status'] == 'executed_unvalidated':
        result['audit_status'] = 'invalid_input_was_not_refused'
    summary['outcomes'].append(result)
    publish()
    if record['status'] == 'adapter_error':
        raise RuntimeError(record)
summary['status'] = 'complete'
publish()
