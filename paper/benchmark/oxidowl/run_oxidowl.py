"""oxidowl on the KM held-out inputs under the KM release protocol.

Per input, three separately measured runs (one core, 240 s, 20 GiB, scoped
watchdog, the protocol/ modules of v170-measure-20261121 with two added
command branches in measure_classification.py):
  cls: oxidowl --max-memory-mb 20480 classification -i <input> -o taxonomy.raw
  ku : oxidowl --max-memory-mb 20480 -k -U <input>
  k  : oxidowl --max-memory-mb 20480 -k <input>
followed by the untimed check audit_oxidowl.py.

  run_oxidowl.py --root R --label L --manifest M --artifact A --task T --job J [--chunk 32] [--only a,b]
"""
import argparse, json, subprocess, sys
from pathlib import Path

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
summary = dict(status='running', baseline='oxidowl', label=args.label, task=args.task, chunk=args.chunk,
               manifest=str(args.manifest), manifest_sha256=digest(args.manifest),
               inventory=str(args.artifact), inventory_sha256=digest(args.artifact), runner_sha256=digest(__file__),
               audit_sha256=digest(args.root / 'audit_oxidowl.py'),
               protocol_sha256={p.name: digest(p) for p in sorted(protocol.glob('*.py'))},
               binary_sha256=inventory['artifacts'][0]['sha256'], only=args.only or None, outcomes=[])


def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)


def brief(record):
    return dict(status=record['status'], exit_code=record.get('exit_code'), wall_s=record.get('wall_s'),
                peak_bytes=record.get('peak_bytes'), error=record.get('error'))


publish()
watchdog.protect_supervisor()
for row in rows:
    output = destination / row['ontology']
    output.mkdir(parents=True)
    cls = measure(inventory, 'oxidowl', row['path'], row['sha256'], output / 'cls', timeout=240, memory_mib=20480)
    ku = measure(inventory, 'oxidowl-ku', row['path'], row['sha256'], output / 'ku', timeout=240, memory_mib=20480)
    k = measure(inventory, 'oxidowl-k', row['path'], row['sha256'], output / 'k', timeout=240, memory_mib=20480)
    result = dict(ontology=row['ontology'], cls=brief(cls), ku=brief(ku), k=brief(k), host=cls.get('host'))
    try:
        import re
        m = re.search(r'Consistency check: (CONSISTENT|INCONSISTENT)', (output / 'k' / 'taxonomy.raw').read_text(errors='replace'))
        result['k_verdict'] = None if not m else m.group(1) == 'CONSISTENT'
        reference = Path(row['reference_directory'])
        result['reference_consistent'] = {b: json.loads((reference / (b + '.validated.json')).read_text()).get('consistent')
                                          for b in ('konclude', 'hermit', 'openllet', 'jfact')
                                          if (reference / (b + '.validated.json')).is_file()}
    except Exception as error:
        result['k_error'] = str(error)
    if cls['status'] == 'executed_unvalidated':
        command = [sys.executable, str(args.root / 'audit_oxidowl.py'), '--out', str(output),
                   '--reference', row['reference_directory'], '--protocol', str(protocol)]
        if ku['status'] == 'executed_unvalidated':
            command.append('--strict')
        try:
            with (output / 'audit.stdout').open('wb') as out, (output / 'audit.stderr').open('wb') as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                        preexec_fn=watchdog.child_preexec)
                execution = watchdog.monitor(proc, timeout=900, memcap_bytes=20480 * 1024**2,
                                             snapshotter=ScopedSnapshot(proc.pid))
            assert execution.status == 'ok' and proc.returncode == 0, 'audit failed: ' + str(execution.status)
            result['audit'] = json.loads((output / 'oxidowl-audit.json').read_text())
        except Exception as error:
            result['audit_error'] = str(error)
    summary['outcomes'].append(result)
    publish()
summary['status'] = 'complete'
publish()
