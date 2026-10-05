"""Capture native baseline contracts on bounded, known-semantics inputs.

These are adapter discovery runs, not performance measurements or correctness
certificates. Keep every exit, output and conversion receipt for semantic audit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

import tree_watchdog as watchdog


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--inventory', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--baseline', choices=['rustdl', 'konclude', 'sequoia', 'more'], required=True)
    args = p.parse_args()
    inventory = {r['id']: r for r in json.loads(args.inventory.read_text())['artifacts']}
    row = inventory[args.baseline]
    assert digest(row['path']) == row['sha256']
    root = args.output / args.baseline
    root.mkdir(parents=True, exist_ok=False)
    prefix = ('Prefix(:=<urn:v145:>)\nPrefix(owl:=<http://www.w3.org/2002/07/owl#>)\n'
              'Ontology(Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C)) '
              'Declaration(NamedIndividual(:i))\n')
    axioms = ['SubClassOf(:A :B) SubClassOf(:B :C)', 'SubClassOf(:A :B)',
              'SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C owl:Nothing)',
              'SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:C owl:Nothing) ClassAssertion(:A :i)',
              'SubClassOf(:A :B) SubClassOf(:B :C)']
    report = {'baseline': args.baseline, 'artifact_sha256': row['sha256'],
              'scope': 'raw adapter contract discovery; semantic audit required', 'cases': []}
    watchdog.protect_supervisor()

    def run(command, stem, env):
        with (root / (stem + '.stdout')).open('wb') as out, (root / (stem + '.stderr')).open('wb') as err:
            proc = subprocess.Popen(command, stdout=out, stderr=err, stdin=subprocess.DEVNULL,
                                    env=env, preexec_fn=watchdog.child_preexec)
            measured = watchdog.monitor(proc, timeout=40, memcap_bytes=2 * 1024**3,
                                        sample_interval=.02)
        return {'command': command, 'exit_code': proc.returncode, 'watchdog_status': measured.status,
                'wall_s': measured.wall_s, 'peak_bytes': measured.peak_bytes}

    env = dict(os.environ)
    env.update(JAVA_OPTS='-Xms128m -Xmx1g -XX:ActiveProcessorCount=1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
    if args.baseline == 'konclude':
        lib = str(Path(row['path']).parent / 'runtime-lib')
        assert Path(lib).is_dir()
        env['LD_LIBRARY_PATH'] = lib + ':' + env.get('LD_LIBRARY_PATH', '')
        hermit = inventory['hermit']
        assert digest(hermit['path']) == hermit['sha256']
        converter_source = Path(__file__).parent / 'ConvertSyntax.java'
        classes = root / 'classes'
        classes.mkdir()
        report['converter_source_sha256'] = digest(converter_source)
        report['converter_compile'] = run(['javac', '--release', '11', '-cp', hermit['path'],
                                          '-d', str(classes), str(converter_source)], 'compile', env)
        assert report['converter_compile']['exit_code'] == 0, 'converter compile failed'
        converter_hash = digest(classes / 'org/kmbenchmark/ConvertSyntax.class')
        report['converter_class_sha256'] = converter_hash
    for i in range(7):
        source = root / f'{i:03}.ofn'
        if i < 5:
            source.write_text(prefix + axioms[i] + '\n)\n')
        elif i == 5:
            source.write_text('Ontology( SubClassOf( broken')
        # Case 6 is an intentionally missing path, not an empty ontology.
        entry = {'case': i, 'source': str(source),
                 'source_sha256': digest(source) if source.exists() else None}
        runtime = source
        if args.baseline == 'konclude' and i < 5:
            runtime = root / f'{i:03}.owlxml'
            conversion = ['java', '-Xmx1g', '-XX:ActiveProcessorCount=1',
                          '-Dkm.converter.sha256=' + converter_hash, '-cp', str(classes) + ':' + hermit['path'],
                          'org.kmbenchmark.ConvertSyntax', str(source), str(runtime),
                          str(root / f'{i:03}.conversion.json'), 'owlxml']
            entry['conversion'] = run(conversion, f'{i:03}.conversion', env)
            if entry['conversion']['exit_code'] != 0 or not runtime.exists():
                report['cases'].append(entry)
                continue
        output = root / f'{i:03}.taxonomy'
        if args.baseline == 'rustdl':
            command = [row['path'], 'classify', '--json', str(runtime)]
        elif args.baseline == 'konclude':
            command = [row['path'], 'classification', '-w', '1', '-v', '-i', str(runtime), '-o', str(output)]
        elif args.baseline == 'sequoia':
            command = [row['path'], '-no-version-check', '-main', 'com.sequoiareasoner.cli.Sequoia', 'classify',
                       '--output', str(output), str(runtime)]
        else:
            command = ['java', '-Xmx1g', '-XX:ActiveProcessorCount=1', '-cp', row['path'],
                       'org.kmbenchmark.FullIriClassifier3',
                       row['factory'], str(runtime), str(output)]
        entry['execution'] = run(command, f'{i:03}', env)
        entry['files'] = {f.name: {'sha256': digest(f), 'bytes': f.stat().st_size}
                          for f in root.glob(f'{i:03}.*') if f.is_file()}
        report['cases'].append(entry)
        (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    report['status'] = 'capture_complete_requires_semantic_audit'
    (root / 'report.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
