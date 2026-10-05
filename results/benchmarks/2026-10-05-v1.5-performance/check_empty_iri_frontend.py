"""Compare frontend output under source-bound entity renaming only."""
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


def compare(old, new, old_meta, new_meta):
    by_iri = {iri: name for name, iri in new_meta['iri_map'].items()}
    assert set(old_meta['iri_map'].values()) == set(by_iri), 'public IRI set changed'
    rename = {name: by_iri[iri] for name, iri in old_meta['iri_map'].items()
              if name != by_iri[iri]}
    # Generated nominal proxies denote their owner's singleton. Bind their
    # renaming through the same source individual, never through list position
    # in the whole ABox. Source-owned proxy names retain the full-IRI binding.
    new_individuals = {entry['individual']: entry
                       for entry in new.get('nominal_abox', {}).get('individuals', [])}
    for entry in old.get('nominal_abox', {}).get('individuals', []):
        updated = new_individuals[rename.get(entry['individual'], entry['individual'])]
        assert len(entry['proxies']) == len(updated['proxies'])
        for before, after in zip(entry['proxies'], updated['proxies']):
            if before in old_meta['iri_map']:
                assert after == rename.get(before, before)
            if before != after:
                assert before not in rename or rename[before] == after
                rename[before] = after
    assert len(set(rename.values())) == len(rename), 'renaming is not injective'

    def renamed(value):
        if isinstance(value, str):
            return rename.get(value, value)
        if isinstance(value, list):
            return [renamed(item) for item in value]
        if isinstance(value, dict):
            return {rename.get(key, key): renamed(item) for key, item in value.items()}
        return value

    def ordered(document, meta):
        if 'nominal_abox' in document:
            document['nominal_abox']['individuals'] = sorted(
                document['nominal_abox'].get('individuals', []),
                key=lambda entry: entry['individual'])
        for key in ['named', 'declared']:
            meta[key] = sorted(meta[key])
        return document, meta

    # Clause bodies, heads, term arguments, role chains, and source expression
    # trees remain ordered and must match exactly. Only unordered name and
    # individual inventories are sorted after renaming.
    assert ordered(renamed(old), renamed(old_meta)) == ordered(new, new_meta), \
        'frontend changed beyond entity names and inventory order'
    return rename


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
    flags = dict(KM_ROUTE='manual', KM_NOMINALS='1', KM_TRIGGER_ABSORB='1', KM_ABSORB='0')
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
        rename = {} if identical else compare(
            json.loads(old.read_text()), json.loads(new.read_text()),
            json.loads(old_meta.read_text()), json.loads(new_meta.read_text()))
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
