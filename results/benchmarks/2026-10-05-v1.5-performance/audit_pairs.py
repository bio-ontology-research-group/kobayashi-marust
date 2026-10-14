"""Audit matched release outputs against existing independent references."""
import json
import os
from pathlib import Path
import subprocess
import sys

from compare_taxonomies import compare
from measure_classification import digest
import tree_watchdog as watchdog


root = Path(__file__).resolve().parent
task = int(os.environ['SLURM_ARRAY_TASK_ID'])
selection = json.loads((root / 'paired-selection.json').read_text())
row = selection['inputs'][task]
binding = json.loads((root / 'audit-references.json').read_text())[row['ontology']]
reference = Path(binding['directory'])
signature = reference / 'signature.tsv'
source_audit = reference / 'audit.json'
assert digest(source_audit) == binding['audit_sha256']
original_audit = json.loads(source_audit.read_text())
assert original_audit['source_sha256'] == row['sha256']
assert digest(row['path']) == row['sha256']
destination = root / ('paired-' + sys.argv[1]) / row['ontology']
assert (destination / 'COMPLETE').exists()
watchdog.protect_supervisor()
outcomes = []
for version in ['v144', 'v145']:
    for repetition in range(selection['repetitions']):
        measured = destination / version / str(repetition)
        record = json.loads((measured / 'record.json').read_text())
        result = dict(version=version, repetition=repetition,
                      measurement_status=record['status'], comparisons={})
        outcomes.append(result)
        if record['status'] != 'executed_unvalidated':
            continue
        try:
            raw = measured / 'taxonomy.raw'
            assert record['source_sha256'] == row['sha256']
            assert digest(raw) == record['files']['taxonomy.raw']['sha256']
            prefix = measured / 'canonical'
            command = [sys.executable, str(root / 'canonicalize.py'),
                       '--input', str(raw), '--format', 'km-json',
                       '--signature', str(signature), '--output-prefix', str(prefix),
                       '--fingerprint-script', str(root / 'full_iri_fingerprint.py')]
            with (measured / 'audit.stdout').open('wb') as out, (measured / 'audit.stderr').open('wb') as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err,
                                        stdin=subprocess.DEVNULL, preexec_fn=watchdog.child_preexec)
                execution = watchdog.monitor(proc, timeout=600, memcap_bytes=20480 * 1024**2)
            assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
            canonical = json.loads(Path(str(prefix) + '.validated.json').read_text())
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                path = reference / (baseline + '.validated.json')
                prior = original_audit['outcomes'].get(baseline, {})
                if prior.get('status') != 'canonicalized_requires_comparison':
                    continue
                assert digest(path) == prior['canonical_sha256']
                result['comparisons'][baseline] = compare(canonical, json.loads(path.read_text()))
            result['verified_solved'] = any(x.get('agreement') is True for x in result['comparisons'].values())
            result['audit_status'] = 'compared'
        except Exception as error:
            result.update(audit_status='audit_error', error=str(error))
summary = dict(ontology=row['ontology'], source_sha256=row['sha256'],
               reference_audit_sha256=binding['audit_sha256'], outcomes=outcomes)
temporary = destination / 'semantic-audit.json.part'
temporary.write_text(json.dumps(summary, indent=2) + '\n')
temporary.replace(destination / 'semantic-audit.json')
if any(r.get('audit_status') == 'audit_error' for r in outcomes):
    raise RuntimeError('one or more semantic audits failed; inspect semantic-audit.json')
