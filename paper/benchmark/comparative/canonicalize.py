"""Strict taxonomy parsing followed by the established full-IRI fingerprint."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from taxonomy import parse, TOP, BOTTOM
from measure_classification import digest


def canonicalize(raw, output_format, signature, output, fingerprint_script):
    lines = Path(signature).read_text().splitlines()
    if not lines or lines[-1] != 'Z\tcomplete':
        raise ValueError('incomplete source signature')
    prefixes, classes = {}, set()
    source_hash = None
    for line in lines[:-1]:
        fields = line.split('\t')
        if fields[0] == 'P' and len(fields) == 3:
            if fields[1] in prefixes:
                raise ValueError('duplicate prefix binding')
            prefixes[fields[1]] = fields[2]
        elif fields[0] == 'C' and len(fields) == 2:
            classes.add(fields[1])
        elif fields == ['M', 'schema', '1']:
            continue
        elif len(fields) == 3 and fields[:2] == ['M', 'source_sha256']:
            if source_hash is not None or len(fields[2]) != 64 or any(c not in '0123456789abcdef' for c in fields[2]):
                raise ValueError('invalid source hash binding')
            source_hash = fields[2]
        else:
            raise ValueError('unexpected source signature record')
    if source_hash is None:
        raise ValueError('source signature has no hash binding')
    data = parse(Path(raw).read_text(), output_format, prefixes=prefixes, expected_classes=classes)
    used = set(data['unsatisfiable']) | {x for pair in data['subsumptions'] for x in pair}
    if used - classes - {TOP, BOTTOM}:
        raise ValueError('taxonomy contains classes outside source signature')
    reported = data['consistent']
    # MORe has no consistency API. Compute a conditional relation fingerprint,
    # but retain unknown consistency and never label it a full verified result.
    data['consistent'] = reported if reported is not None else True
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    normalized = Path(str(output) + '.normalized.json')
    with normalized.open('w') as stream:
        json.dump(data, stream, separators=(',', ':'))
    command = [sys.executable, str(fingerprint_script), '--input', str(normalized), '--format', 'json',
               '--output-prefix', str(output)]
    run = subprocess.run(command, capture_output=True, text=True, check=True)
    record = json.loads(run.stdout)
    record.update(reported_consistency=reported, validation_scope='taxonomy_only' if reported is None else 'consistency_and_taxonomy',
                  raw_sha256=digest(raw), source_sha256=source_hash, source_signature_sha256=digest(signature),
                  strict_adapter_sha256=digest(Path(__file__).with_name('taxonomy.py')),
                  canonicalizer_sha256=digest(__file__), fingerprint_script_sha256=digest(fingerprint_script))
    target = Path(str(output) + '.validated.json')
    target.write_text(json.dumps(record, indent=2) + '\n')
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--format', required=True)
    parser.add_argument('--signature', type=Path, required=True)
    parser.add_argument('--output-prefix', type=Path, required=True)
    parser.add_argument('--fingerprint-script', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(canonicalize(args.input, args.format, args.signature, args.output_prefix, args.fingerprint_script)))
