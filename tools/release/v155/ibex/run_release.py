"""Measure KM inputs under the v1.5.3 protocol and audit answers against the pinned references.

This is `run_combined.py` of the v1.5.4 G8 run (`g8-v154-80c8f82a/`) with the
manifest, artifact inventory, destination and chunk taken from the command
line, and one added field per outcome (`wrong`, defined as in
`run_paired.py`: some reference disagrees and none agrees). The measurement
and audit modules (`measure_classification.py`, `tree_watchdog.py`,
`scoped_snapshot.py`, `timing_support.py`, `canonicalize.py`, `taxonomy.py`,
`compare_taxonomies.py`, `full_iri_fingerprint.py`) are byte-identical copies
of the v1.5.4 G8 run's modules under `<root>/protocol/` (checked by
`files.sha256` before every task): one core, 240 s, 20 GiB, scoped watchdog.

  run_release.py --root R --label L --manifest M --artifact A --task T --job J
                 [--chunk 32] [--only ont1,ont2,...] [--expect-inputs N]
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ap = argparse.ArgumentParser()
ap.add_argument('--root', required=True, type=Path)
ap.add_argument('--label', required=True)
ap.add_argument('--manifest', required=True, type=Path)
ap.add_argument('--artifact', required=True, type=Path)
ap.add_argument('--task', required=True, type=int)
ap.add_argument('--job', required=True)
ap.add_argument('--chunk', type=int, default=32)
ap.add_argument('--only', default='')
ap.add_argument('--expect-inputs', type=int, default=0)
args = ap.parse_args()

protocol = args.root / 'protocol'
sys.path.insert(0, str(protocol))
from compare_taxonomies import compare  # noqa: E402
from measure_classification import digest, measure  # noqa: E402
import tree_watchdog as watchdog  # noqa: E402
from scoped_snapshot import ScopedSnapshot  # noqa: E402

manifest = json.loads(args.manifest.read_text())
inventory = json.loads(args.artifact.read_text())
flags = dict(inventory['flags'])
os.environ.update(flags)
if args.expect_inputs:
    assert len(manifest['inputs']) == args.expect_inputs, (len(manifest['inputs']), args.expect_inputs)
if args.only:
    wanted = args.only.split(',')
    by_name = {r['ontology']: r for r in manifest['inputs']}
    selected = [by_name[o] for o in wanted]
else:
    selected = manifest['inputs']
rows = selected[args.task * args.chunk:(args.task + 1) * args.chunk]
assert 1 <= len(rows) <= args.chunk
destination = args.root / (args.label + '-' + args.job)
summary_path = destination / 'chunks' / (str(args.task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', label=args.label, task=args.task, chunk=args.chunk,
               manifest=str(args.manifest), manifest_sha256=digest(args.manifest),
               inventory=str(args.artifact), inventory_sha256=digest(args.artifact),
               runner_sha256=digest(__file__),
               protocol_sha256={p.name: digest(p) for p in sorted(protocol.glob('*.py'))},
               binary_sha256=[a['sha256'] for a in inventory['artifacts'] if a['id'] == 'km'][0],
               flags=flags, only=args.only or None, outcomes=[])


def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)


publish()
watchdog.protect_supervisor()
for row in rows:
    output = destination / row['ontology']
    record = measure(inventory, 'km', row['path'], row['sha256'], output, timeout=240, memory_mib=20480)
    result = dict(ontology=row['ontology'], input_admission=row['input_admission'],
                  measurement_status=record['status'], wall_s=record.get('wall_s'),
                  peak_bytes=record.get('peak_bytes'), host=record.get('host'), verified_solved=False,
                  wrong=False, comparisons={}, measurement_sha256=digest(output / 'record.json'))
    if record['status'] == 'executed_unvalidated' and row['input_admission'] == 'checks_passed':
        try:
            reference = Path(row['reference_directory'])
            assert digest(reference / 'audit.json') == row['reference_audit_sha256']
            audit = json.loads((reference / 'audit.json').read_text())
            assert audit['source_sha256'] == row['sha256']
            prefix = output / 'canonical'
            command = [sys.executable, str(protocol / 'canonicalize.py'),
                       '--input', str(output / 'taxonomy.raw'), '--format', 'km-json',
                       '--signature', str(reference / 'signature.tsv'),
                       '--output-prefix', str(prefix),
                       '--fingerprint-script', str(protocol / 'full_iri_fingerprint.py')]
            with (output / 'audit.stdout').open('wb') as out, (output / 'audit.stderr').open('wb') as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                        preexec_fn=watchdog.child_preexec)
                execution = watchdog.monitor(proc, timeout=600, memcap_bytes=20480 * 1024**2,
                                             snapshotter=ScopedSnapshot(proc.pid))
            result['audit_execution'] = dict(status=execution.status, exit_code=proc.returncode,
                                             wall_s=execution.wall_s, peak_bytes=execution.peak_bytes,
                                             timeout_s=600, memory_mib=20480)
            assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
            answer = json.loads((output / 'canonical.validated.json').read_text())
            result['relation_sha256'] = answer.get('relation_sha256')
            result['reported_consistency'] = answer.get('reported_consistency')
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                prior = audit['outcomes'].get(baseline, {})
                if prior.get('status') != 'canonicalized_requires_comparison':
                    continue
                path = reference / (baseline + '.validated.json')
                assert digest(path) == prior['canonical_sha256']
                result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
            result['verified_solved'] = any(x.get('agreement') is True for x in result['comparisons'].values())
            result['wrong'] = (any(x.get('agreement') is False for x in result['comparisons'].values())
                               and not result['verified_solved'])
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
