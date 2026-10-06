"""Check the source-GCI padding obligation, never production admission.

Reject duplicate JSON keys before Lean's map-based parser sees the document.
Pass byte-identical private snapshots of the complete source and witness to the
Lean checker and bind their hashes in a receipt. Source decoding is executable
but not yet proved equivalent to Rust/OWL semantics; the other admission and
reverse-model obligations remain open.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(data):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f'duplicate JSON key: {key}')
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError(f'non-JSON numeric constant: {value}')

    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid_constant)


def check(source, witness, lake='lake'):
    repo = Path(__file__).resolve().parents[3]
    source_bytes, witness_bytes = source.read_bytes(), witness.read_bytes()
    receipt = dict(scope='source-GCI padding obligation only', release_approved=False,
                   source_sha256=sha(source_bytes), witness_sha256=sha(witness_bytes),
                   accepted=False, source_ast_padding_lowering_proved=True,
                   decoder_semantic_equivalence_proved=False)
    files = ['lean/DatatypePaddingWitnessCheck.lean',
             'lean/ContextCalculus/DatatypePaddingSource.lean',
             'lean/ContextCalculus/DatatypePaddingCheck.lean',
             'lean/ContextCalculus/DatatypePadding.lean',
             'lean/ContextCalculus/DatatypeClassTransport.lean',
             'lean/ContextCalculus/FunctionalDatatypeQuotient.lean',
             'lean/lean-toolchain']
    receipt['checker_sources'] = {name: sha((repo / name).read_bytes()) for name in files}
    receipt['driver_sha256'] = sha(Path(__file__).read_bytes())
    try:
        for data in (source_bytes, witness_bytes):
            if not isinstance(strict_json(data), dict):
                raise ValueError('source and witness must be JSON objects')
    except (ValueError, UnicodeError) as error:
        receipt['error'] = str(error)
        return receipt
    # Rebuild imported proof modules from the recorded source, so a stale olean
    # cannot make a source-hash receipt appear to cover an unchecked edit.
    try:
        build = subprocess.run([lake, 'build', 'ContextCalculus.DatatypePaddingSource'],
                               cwd=repo / 'lean', capture_output=True, text=True, timeout=60)
        build_log = build.stdout + build.stderr
        receipt['proof_build_exit_code'] = build.returncode
        receipt['proof_build_log_sha256'] = sha(build_log.encode())
        if build.returncode != 0 or 'sorryAx' in build_log:
            receipt['error'] = 'proof build failed or reported sorryAx'
            receipt['proof_build_log'] = build_log
            return receipt
    except (OSError, subprocess.TimeoutExpired) as error:
        receipt['error'] = str(error)
        return receipt
    with tempfile.TemporaryDirectory(prefix='km-padding-check-') as tmp:
        source_copy, witness_copy = Path(tmp) / 'source.json', Path(tmp) / 'witness.json'
        source_copy.write_bytes(source_bytes)
        witness_copy.write_bytes(witness_bytes)
        source_copy.chmod(0o400)
        witness_copy.chmod(0o400)
        command = [lake, 'env', 'lean', '--run', 'DatatypePaddingWitnessCheck.lean',
                   str(source_copy), str(witness_copy)]
        try:
            result = subprocess.run(command, cwd=repo / 'lean', capture_output=True,
                                    text=True, timeout=60)
            receipt.update(exit_code=result.returncode, stdout=result.stdout,
                           stderr=result.stderr, accepted=result.returncode == 0)
        except (OSError, subprocess.TimeoutExpired) as error:
            receipt['error'] = str(error)
    if any(sha((repo / name).read_bytes()) != digest
           for name, digest in receipt['checker_sources'].items()):
        receipt.update(accepted=False, error='checker source changed during verification')
    return receipt


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('witness', type=Path)
    parser.add_argument('--lake', default='lake')
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    result = check(args.source, args.witness, args.lake)
    serialized = json.dumps(result, indent=2) + '\n'
    if args.receipt:
        with args.receipt.open('x') as output:
            output.write(serialized)
    print(serialized, end='')
    raise SystemExit(0 if result['accepted'] else 1)
