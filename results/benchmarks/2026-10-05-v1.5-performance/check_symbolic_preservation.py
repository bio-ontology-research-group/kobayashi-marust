"""Bounded, byte-exact audit of all symbolic frontend evidence fields."""
import argparse
import json
import os
from pathlib import Path
import subprocess

from check_empty_iri_frontend_auto import digest
import tree_watchdog as watchdog


def main():
    parser = argparse.ArgumentParser()
    for name in ['old', 'new', 'source', 'output']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env.update(KM_THREADS='1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
    receipt = dict(source_sha256=digest(args.source), runs={}, byte_identical=False,
                   scope='All symbolic frontend evidence fields; no reasoning or performance claim.',
                   limits=dict(seconds_per_run=240, memory_gib=20, cpus=1))
    cpu = min(os.sched_getaffinity(0))

    def prepare():
        watchdog.child_preexec()
        os.sched_setaffinity(0, {cpu})

    def save():
        (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')

    save()
    for label in ['old', 'new']:
        binary = getattr(args, label).resolve()
        output = args.output / (label + '.jsonl')
        with (args.output / (label + '.stdout')).open('wb') as out, \
                (args.output / (label + '.stderr')).open('wb') as err:
            process = subprocess.Popen([str(binary), str(args.source.resolve()), str(output)],
                                       env=env, stdout=out, stderr=err, preexec_fn=prepare)
            result = watchdog.monitor(process, timeout=240, memcap_bytes=20 * 1024**3)
        receipt['runs'][label] = dict(binary_sha256=digest(binary), status=result.status,
                                     returncode=process.returncode, peak_bytes=result.peak_bytes,
                                     wall_s=result.wall_s)
        if result.status != 'ok' or process.returncode != 0:
            save()
            raise SystemExit(1)
        receipt['runs'][label].update(output_sha256=digest(output), output_bytes=output.stat().st_size)
        save()
    receipt['byte_identical'] = receipt['runs']['old']['output_sha256'] == receipt['runs']['new']['output_sha256']
    save()
    raise SystemExit(0 if receipt['byte_identical'] else 1)


if __name__ == '__main__':
    main()
