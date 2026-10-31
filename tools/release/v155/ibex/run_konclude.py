"""Same-day Konclude run with the binary and settings of the 2026-10-04 run.

Konclude settings are those of `v145-comparative-20261004/konclude-panel-v1/
run_konclude_panel.py` (array 53201252): the Konclude build
`konclude-v0.7.0-1138-build-20260721-03/Konclude-build-a` (sha256 e8dd5373...),
command `classification -w 1 -v -i <input.owlxml> -o taxonomy.raw`, one core,
240 s, 20 GiB, the verified OWL/XML conversion of each source. The conversion
is not timed in either run; this runner reuses the 2026-10-04 conversion
(`classification-konclude-53201252/conversion/<ontology>/`), whose receipt
`measure()` checks again (source hash, output hash, round-trip axiom and
signature equality). Measurement uses the scoped-watchdog module of the
v1.5.3 protocol (`<root>/protocol/measure_classification.py`), as the KM runs
do; the 2026-10-04 run used the pre-scoped module.

Each answer is canonicalised (`canonicalize.py --format owlxml`) and compared
with the pinned Konclude 2026-10-04, HermiT, Openllet and JFact answers, so
the aggregation can check that the same-day answer equals the 2026-10-04 one.

  run_konclude.py --root R --label L --manifest M --artifact A --task T --job J
                  [--chunk 32] [--only ont1,...]
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

CONVERSIONS = Path('/ibex/scratch/projects/c2014/hohndor/km/v145-comparative-20261004/classification-konclude-53201252/conversion')

ap = argparse.ArgumentParser()
ap.add_argument('--root', required=True, type=Path)
ap.add_argument('--label', required=True)
ap.add_argument('--manifest', required=True, type=Path)
ap.add_argument('--artifact', required=True, type=Path)
ap.add_argument('--task', required=True, type=int)
ap.add_argument('--job', required=True)
ap.add_argument('--chunk', type=int, default=32)
ap.add_argument('--only', default='')
args = ap.parse_args()

protocol = args.root / 'protocol'
sys.path.insert(0, str(protocol))
from compare_taxonomies import compare  # noqa: E402
from measure_classification import digest, measure  # noqa: E402
import tree_watchdog as watchdog  # noqa: E402
from scoped_snapshot import ScopedSnapshot  # noqa: E402

manifest = json.loads(args.manifest.read_text())
inventory = json.loads(args.artifact.read_text())
if args.only:
    by_name = {r['ontology']: r for r in manifest['inputs']}
    selected = [by_name[o] for o in args.only.split(',')]
else:
    selected = manifest['inputs']
rows = selected[args.task * args.chunk:(args.task + 1) * args.chunk]
assert 1 <= len(rows) <= args.chunk
destination = args.root / (args.label + '-' + args.job)
summary_path = destination / 'chunks' / (str(args.task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', baseline='konclude', label=args.label, task=args.task, chunk=args.chunk,
               manifest=str(args.manifest), manifest_sha256=digest(args.manifest),
               inventory=str(args.artifact), inventory_sha256=digest(args.artifact),
               runner_sha256=digest(__file__),
               protocol_sha256={p.name: digest(p) for p in sorted(protocol.glob('*.py'))},
               binary_sha256=[a['sha256'] for a in inventory['artifacts'] if a['id'] == 'konclude'][0],
               conversions=str(CONVERSIONS), only=args.only or None, outcomes=[])


def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)


publish()
watchdog.protect_supervisor()
for row in rows:
    output = destination / row['ontology']
    conv = CONVERSIONS / row['ontology']
    result = dict(ontology=row['ontology'], input_admission=row['input_admission'], verified_solved=False,
                  wrong=False, comparisons={})
    try:
        crec = json.loads((conv / 'record.json').read_text())
        assert crec['status'] == 'converted' and crec['source_sha256'] == row['sha256'], 'no verified 2026-10-04 conversion'
        assert digest(conv / 'input.owlxml') == crec['runtime_source_sha256'], 'conversion output changed'
        assert digest(conv / 'roundtrip.tsv') == crec['receipt_sha256'], 'conversion receipt changed'
    except Exception as error:
        result.update(measurement_status='input_conversion_unavailable', error=str(error))
        summary['outcomes'].append(result)
        publish()
        continue
    record = measure(inventory, 'konclude', row['path'], row['sha256'], output, conv / 'input.owlxml',
                     crec['runtime_source_sha256'], timeout=240, memory_mib=20480,
                     conversion_receipt=conv / 'roundtrip.tsv')
    result.update(measurement_status=record['status'], exit_code=record.get('exit_code'),
                  wall_s=record.get('wall_s'), peak_bytes=record.get('peak_bytes'), host=record.get('host'),
                  measurement_sha256=digest(output / 'record.json'))
    if record['status'] == 'executed_unvalidated' and row['input_admission'] == 'checks_passed':
        try:
            reference = Path(row['reference_directory'])
            assert digest(reference / 'audit.json') == row['reference_audit_sha256']
            audit = json.loads((reference / 'audit.json').read_text())
            command = [sys.executable, str(protocol / 'canonicalize.py'),
                       '--input', str(output / 'taxonomy.raw'), '--format', 'owlxml',
                       '--signature', str(reference / 'signature.tsv'),
                       '--output-prefix', str(output / 'canonical'),
                       '--fingerprint-script', str(protocol / 'full_iri_fingerprint.py')]
            with (output / 'audit.stdout').open('wb') as out, (output / 'audit.stderr').open('wb') as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                        preexec_fn=watchdog.child_preexec)
                execution = watchdog.monitor(proc, timeout=600, memcap_bytes=20480 * 1024**2,
                                             snapshotter=ScopedSnapshot(proc.pid))
            assert execution.status == 'ok' and proc.returncode == 0, 'canonicalization failed'
            answer = json.loads((output / 'canonical.validated.json').read_text())
            result['relation_sha256'] = answer.get('relation_sha256')
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                prior = audit['outcomes'].get(baseline, {})
                if prior.get('status') != 'canonicalized_requires_comparison':
                    continue
                path = reference / (baseline + '.validated.json')
                assert digest(path) == prior['canonical_sha256']
                result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
            others = [v for k, v in result['comparisons'].items() if k != 'konclude']
            result['same_answer_as_20261004'] = result['comparisons'].get('konclude', {}).get('agreement') is True
            result['verified_solved'] = any(x.get('agreement') is True for x in others)
            result['wrong'] = any(x.get('agreement') is False for x in others) and not result['verified_solved']
            result['audit_status'] = 'compared'
        except Exception as error:
            result.update(audit_status='audit_error', error=str(error))
    summary['outcomes'].append(result)
    publish()
    if record['status'] == 'adapter_error':
        raise RuntimeError(record)
summary['status'] = 'complete'
publish()
