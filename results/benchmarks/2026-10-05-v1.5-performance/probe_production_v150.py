"""Bounded workstation phase traces; not release benchmark timings."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from compare_taxonomies import compare
from measure_classification import digest
import tree_watchdog as watchdog


def probe(binary, directory, output):
    root = Path(__file__).resolve().parent
    inventory_path = root / 'production-v150-full-artifact.json'
    inventory = json.loads(inventory_path.read_text())
    assert digest(binary) == inventory['artifacts'][0]['sha256']
    inputs_path = directory / 'inputs.json'
    inputs = json.loads(inputs_path.read_text())['inputs']
    output.mkdir(parents=True, exist_ok=False)
    for key in list(os.environ):
        if key.startswith('KM_'):
            del os.environ[key]
    flags = dict(inventory['flags'], KM_THREADS='1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
    os.environ.update(flags)
    cpu = min(os.sched_getaffinity(0))

    def child():
        watchdog.child_preexec()
        os.sched_setaffinity(0, {cpu})

    def run(command, stdout, stderr, timeout):
        with stdout.open('wb') as out, stderr.open('wb') as err:
            process = subprocess.Popen(command, stdout=out, stderr=err,
                                       stdin=subprocess.DEVNULL, preexec_fn=child)
            watched = watchdog.monitor(process, timeout=timeout, memcap_bytes=20 * 1024**3)
        return process.returncode, watched

    watchdog.protect_supervisor()
    results = []
    for row in inputs:
        name = row['ontology']
        source, reference = directory / (name + '.owl'), directory / name
        assert digest(source) == row['sha256']
        assert digest(reference / 'audit.json') == row['reference_audit_sha256']
        audit = json.loads((reference / 'audit.json').read_text())
        assert audit['source_sha256'] == row['sha256']
        dest = output / name
        dest.mkdir()
        exit_code, watched = run([str(binary), 'classify', str(source)],
                                 dest / 'taxonomy.raw', dest / 'stderr', 30)
        result = dict(ontology=name, source_sha256=row['sha256'], exit_code=exit_code,
                      status=watched.status, wall_s=watched.wall_s, peak_bytes=watched.peak_bytes,
                      verified_solved=False, comparisons={},
                      stderr_sha256=digest(dest / 'stderr'), taxonomy_sha256=digest(dest / 'taxonomy.raw'))
        if watched.status == 'ok' and exit_code == 0:
            code, checked = run([sys.executable, str(root / 'canonicalize.py'),
                                 '--input', str(dest / 'taxonomy.raw'), '--format', 'km-json',
                                 '--signature', str(reference / 'signature.tsv'),
                                 '--output-prefix', str(dest / 'canonical'),
                                 '--fingerprint-script', str(root / 'full_iri_fingerprint.py')],
                                dest / 'audit.stdout', dest / 'audit.stderr', 60)
            assert code == 0 and checked.status == 'ok', name
            answer = json.loads((dest / 'canonical.validated.json').read_text())
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                prior = audit['outcomes'].get(baseline, {})
                if prior.get('status') != 'canonicalized_requires_comparison':
                    continue
                path = reference / (baseline + '.validated.json')
                assert digest(path) == prior['canonical_sha256']
                result['comparisons'][baseline] = compare(answer, json.loads(path.read_text()))
            result['verified_solved'] = any(r.get('agreement') is True
                                           for r in result['comparisons'].values())
        result['phase_lines'] = [line for line in (dest / 'stderr').read_text().splitlines()
                                 if 'KM_TIMING' in line or 'CONFORMANCE' in line]
        results.append(result)
    summary = dict(diagnostic_only=True, release_approved=False, timeout_s=30, memory_gib=20,
                   cpu=cpu, cpu_count=1, flags=flags, binary_sha256=digest(binary),
                   inventory_sha256=digest(inventory_path), inputs_sha256=digest(inputs_path),
                   runner_sha256=digest(Path(__file__)), watchdog_sha256=digest(Path(watchdog.__file__)),
                   rows=results,
                   scope='Local production-binary correctness check on three cases near the partial sweep median. '
                         'Not a release speed comparison or a new full-corpus solved count.')
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    return summary


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = probe(args.binary.resolve(), args.directory.resolve(), args.output.resolve())
    print(json.dumps([{'ontology': r['ontology'], 'verified': r['verified_solved'],
                       'wall_s': r['wall_s'], 'phase_lines': r['phase_lines']} for r in result['rows']], indent=2))
