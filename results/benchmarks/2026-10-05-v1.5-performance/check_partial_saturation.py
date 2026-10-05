"""Single-CPU bounded interruption diagnostics, not release performance metrics."""
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
    parser.add_argument('--cap', type=int)
    parser.add_argument('--timeout', type=int, default=45)
    parser.add_argument('--route', choices=['auto', 'ht_bridge'], default='auto')
    parser.add_argument('--ground-source', action='store_true', help='Probe the existing exact source compiler.')
    parser.add_argument('--dump-typed', action='store_true', help='Save the converted input for admission diagnosis.')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    flags = dict(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
                 KM_BRIDGE_PROGRESS='1', KM_TIMING='1', KM_HT_STATS='1',
                 KM_ROUTE=args.route, KM_THREADS='1',
                 OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
    if args.cap is not None:
        flags['KM_HT_SATURATION_BUDGET_CAP_S'] = str(args.cap)
    if args.ground_source:
        flags['KM_GROUND_RULE_SOURCE'] = '1'
    if args.dump_typed:
        flags['KM_DUMP_TIN'] = str((args.output / 'typed-input.json').resolve())
    environment = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    environment.update(flags)
    cpu = min(os.sched_getaffinity(0))
    raw, stderr = args.output / 'taxonomy.json', args.output / 'stderr'
    started = time.monotonic()
    timed_out = False
    with raw.open('w') as out, stderr.open('w') as err:
        process = subprocess.Popen(
            [str(args.binary.resolve()), 'classify', '--route', args.route,
             str(args.source.resolve())],
            env=environment, stdout=out, stderr=err, start_new_session=True,
            preexec_fn=lambda: os.sched_setaffinity(0, {cpu}))
        try:
            process.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    receipt = dict(diagnostic_only=True, source_sha256=digest(args.source),
                   binary_sha256=digest(args.binary), runner_sha256=digest(__file__),
                   flags=flags, cpu_affinity=[cpu], timeout_s=args.timeout,
                   timed_out=timed_out, returncode=process.returncode,
                   wall_s=time.monotonic()-started, raw_sha256=digest(raw),
                   stderr_sha256=digest(stderr),
                   partial_pass_discarded='BRIDGE-SATURATION-DISCARDED:' in stderr.read_text())
    if process.returncode == 0:
        validated = canonicalize(raw, 'km-json', args.references / 'signature.tsv',
                                 args.output / 'canonical',
                                 Path(__file__).with_name('full_iri_fingerprint.py'))
        assert validated['source_sha256'] == receipt['source_sha256']
        receipt['comparisons'] = {
            ref.stem: compare(validated, json.loads(ref.read_text()))
            for ref in sorted(args.references.glob('*.validated.json'))
        }
    (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
