"""Bounded ORE 15167 regression check; these times are not release metrics."""
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
    parser.add_argument('--binary', required=True, type=Path)
    parser.add_argument('--source', required=True, type=Path)
    parser.add_argument('--references', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    source_hash = digest(args.source)
    assert source_hash == '643bf3b09cb460eb375adc193ce9ce437bb87bdadfde87c24510f38959144478'
    args.output.mkdir(parents=True, exist_ok=True)
    rows = []
    for route in ['ht_bridge', 'auto']:
        prefix = args.output / route
        command = [str(args.binary.resolve()), 'classify']
        if route != 'auto':
            command += ['--route', route]
        command.append(str(args.source.resolve()))
        flags = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
                     KM_HT_SATURATION_BUDGET_CAP_S='1', KM_BRIDGE_PROGRESS='1')
        environment = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
        environment.update(flags)
        raw = prefix.with_suffix('.json')
        stderr = prefix.with_suffix('.stderr')
        started = time.monotonic()
        timed_out = False
        with raw.open('w') as out, stderr.open('w') as err:
            process = subprocess.Popen(command, env=environment, stdout=out, stderr=err,
                                       start_new_session=True)
            try:
                process.wait(timeout=15)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
        row = dict(route=route, flags=flags, returncode=process.returncode,
                   timed_out=timed_out, wall_s=time.monotonic()-started,
                   raw_sha256=digest(raw), stderr_sha256=digest(stderr))
        if process.returncode == 0:
            validated = canonicalize(raw, 'km-json', args.references / 'signature.tsv',
                                     prefix, Path(__file__).with_name('full_iri_fingerprint.py'))
            assert validated['source_sha256'] == source_hash
            row['comparisons'] = {
                name: compare(validated, json.loads((args.references / (name+'.validated.json')).read_text()))
                for name in ['konclude', 'hermit', 'openllet', 'jfact']
            }
        rows.append(row)
    receipt = dict(diagnostic_only=True, source_sha256=source_hash,
                   binary_sha256=digest(args.binary), runner_sha256=digest(__file__), rows=rows,
                   scope='One-second optional saturation cap; automatic and explicit bridge routes. Not a default-configuration benchmark.')
    (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))
    assert all(row['returncode'] == 0 and
               all(c['agreement'] is True for c in row['comparisons'].values()) for row in rows)


if __name__ == '__main__':
    main()
