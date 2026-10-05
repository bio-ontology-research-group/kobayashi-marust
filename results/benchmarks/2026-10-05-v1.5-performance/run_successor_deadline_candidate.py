"""Measure every frozen input and audit completed answers against pinned references."""
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
inventory_path = root / 'successor-deadline-candidate-artifact.json'
inventory = json.loads(inventory_path.read_text())
flags = {'KM_HT_DDB': '1', 'KM_HT_NATIVE_FULL': '1', 'KM_CACHE_CONFORMANCE': '1', 'KM_HT_SATURATION_BUDGET_CAP_S': '1'}
os.environ.update(flags)
rows = manifest['inputs'][task * 32:(task + 1) * 32]
assert len(manifest['inputs']) == 1920 and len(rows) == 32
destination = root / ('successor-deadline-candidate-' + os.environ['SLURM_ARRAY_JOB_ID'])
summary_path = destination / 'chunks' / (str(task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', manifest_sha256=digest(manifest_path),
               inventory_sha256=digest(inventory_path), runner_sha256=digest(__file__),
               flags=flags, outcomes=[])


def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)


publish()
watchdog.protect_supervisor()
for row in rows:
    output = destination / row['ontology']
    record = measure(inventory, 'km', row['path'], row['sha256'], output,
                     timeout=240, memory_mib=20480)
    result = dict(ontology=row['ontology'], input_admission=row['input_admission'],
                  measurement_status=record['status'], wall_s=record.get('wall_s'),
                  peak_bytes=record.get('peak_bytes'), verified_solved=False,
                  comparisons={}, measurement_sha256=digest(output / 'record.json'))
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
            assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
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
