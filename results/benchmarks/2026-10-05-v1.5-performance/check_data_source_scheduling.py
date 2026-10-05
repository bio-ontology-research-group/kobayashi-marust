"""Audit automatic recovery of five data-ABox timeout cases. Diagnostic only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

from canonicalize import canonicalize
from compare_taxonomies import compare


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--sources', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cap', type=int, help='Optional saturation cap; default keeps the production budget.')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / 'full-candidate-inputs.json').read_text())['inputs']
    args.output.mkdir(parents=True, exist_ok=True)
    rows = []
    for number in ['3843', '4719', '586', '7342', '7828']:
        name = 'ore_ont_' + number
        entry = next(row for row in manifest if row['ontology'] == name)
        source = args.sources / (name + '.owl')
        refs = args.sources / ('3843-references' if number == '3843' else name + '-references')
        assert digest(source) == entry['sha256']
        assert digest(refs / 'audit.json') == entry['reference_audit_sha256']
        prior = json.loads((refs / 'audit.json').read_text())
        prefix = args.output / name
        raw, stderr = prefix.with_suffix('.json'), prefix.with_suffix('.stderr')
        flags = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
                     KM_TIMING='1', KM_THREADS='1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
        if args.cap is not None:
            flags['KM_HT_SATURATION_BUDGET_CAP_S'] = str(args.cap)
        env = {key: value for key, value in os.environ.items() if not key.startswith('KM_')}
        env.update(flags)
        cpu = min(os.sched_getaffinity(0))
        started = time.monotonic()
        with raw.open('w') as out, stderr.open('w') as err:
            process = subprocess.Popen([str(args.binary.resolve()), 'classify', str(source)],
                                       env=env, stdout=out, stderr=err, start_new_session=True,
                                       preexec_fn=lambda: os.sched_setaffinity(0, {cpu}))
            try:
                process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        row = dict(ontology=name, source_sha256=entry['sha256'], flags=flags, cpu_affinity=[cpu],
                   returncode=process.returncode, wall_s=time.monotonic()-started,
                   raw_sha256=digest(raw), stderr_sha256=digest(stderr),
                   automatic_reduction_selected='automatic data source accepted: KM_GROUND_RULE_SOURCE'
                   in stderr.read_text(), comparisons={})
        if process.returncode == 0:
            answer = canonicalize(raw, 'km-json', refs / 'signature.tsv', prefix,
                                  root / 'full_iri_fingerprint.py')
            for baseline in ['konclude', 'hermit', 'openllet', 'jfact']:
                reference = refs / (baseline + '.validated.json')
                assert digest(reference) == prior['outcomes'][baseline]['canonical_sha256']
                row['comparisons'][baseline] = compare(answer, json.loads(reference.read_text()))
        rows.append(row)
        print(name, row['returncode'], row['wall_s'], row['automatic_reduction_selected'], flush=True)
    receipt = dict(diagnostic_only=True, binary_sha256=digest(args.binary),
                   runner_sha256=digest(__file__), rows=rows,
                   scope='Bounded local automatic-route checks, not full-corpus release metrics.')
    (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    assert all(row['returncode'] == 0 and row['automatic_reduction_selected'] and
               all(c['agreement'] is True for c in row['comparisons'].values()) for row in rows)


if __name__ == '__main__':
    main()
