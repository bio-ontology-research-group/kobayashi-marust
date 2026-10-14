"""Require byte-identical frontend outputs under automatic routing."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def digest(path):
    value = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(block)
    return value.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--old', type=Path, required=True)
    parser.add_argument('--new', type=Path, required=True)
    parser.add_argument('--source', type=Path, action='append', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=60)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith('KM_')}
    flags = dict(KM_ROUTE='auto', KM_THREADS='1')
    env.update(OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1')
    env.update(flags)
    rows = []
    for source in args.source:
        outputs = {}
        for label, binary in [('old', args.old), ('new', args.new)]:
            stem = args.output / (source.stem + '-' + label)
            raw, meta = stem.with_suffix('.json'), stem.with_suffix('.meta.json')
            with raw.open('wb') as out:
                result = subprocess.run([str(binary.resolve()), 'ofn', str(source.resolve()),
                                         '--meta', str(meta)], env=env, stdout=out,
                                        stderr=subprocess.PIPE, timeout=args.timeout)
            assert result.returncode == 0, result.stderr.decode()
            outputs[label] = (raw, meta)
        old, old_meta = outputs['old']; new, new_meta = outputs['new']
        old_hash, new_hash = digest(old), digest(new)
        old_meta_hash, new_meta_hash = digest(old_meta), digest(new_meta)
        identical = old_hash == new_hash and old_meta_hash == new_meta_hash
        assert identical, 'Automatic frontend clause or metadata bytes changed'
        rename = {}
        rows.append(dict(source=str(source), source_sha256=digest(source), renaming=rename,
                         old_sha256=old_hash, new_sha256=new_hash,
                         old_meta_sha256=old_meta_hash, new_meta_sha256=new_meta_hash,
                         byte_identical=identical,
                         equal_after_source_bound_renaming=True))
    receipt = dict(old_binary_sha256=digest(args.old), new_binary_sha256=digest(args.new),
                   runner_sha256=digest(__file__), flags=flags, rows=rows,
                   scope='Only the listed sources; this is not a full-corpus frontend gate.')
    (args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
