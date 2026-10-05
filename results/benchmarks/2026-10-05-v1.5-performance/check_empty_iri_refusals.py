"""Verify byte-identical refusals on frozen inputs already adjudicated invalid."""
import argparse
import json
import os
import re
from pathlib import Path
import subprocess
from check_empty_iri_frontend import digest

parser = argparse.ArgumentParser()
parser.add_argument('--old', required=True, type=Path)
parser.add_argument('--new', required=True, type=Path)
parser.add_argument('--source', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
parser.add_argument('--timeout', type=int, default=240)
args = parser.parse_args()
args.output.mkdir(parents=True, exist_ok=True)
env = {k:v for k,v in os.environ.items() if not k.startswith('KM_')}
flags = dict(KM_ROUTE='manual', KM_NOMINALS='1', KM_TRIGGER_ABSORB='1', KM_ABSORB='0')
env.update(flags)
outputs = {}
for label, binary in [('old', args.old), ('new', args.new)]:
    stem = args.output / (args.source.stem + '-' + label)
    raw, meta, error = stem.with_suffix('.json'), stem.with_suffix('.meta.json'), stem.with_suffix('.stderr')
    with raw.open('wb') as out, error.open('wb') as err:
        result = subprocess.run([str(binary.resolve()), 'ofn', str(args.source.resolve()),
                                 '--meta', str(meta)], env=env, stdout=out, stderr=err,
                                timeout=args.timeout)
    assert result.returncode >= 0, 'Signal death cannot establish preservation'
    if result.returncode > 0:
        assert re.search(rb'\binvalid OWL 2 DL input(?::| at line [0-9]+:)', error.read_bytes()), \
            'Expected an OWL 2 DL admission refusal'
    outputs[label] = dict(returncode=result.returncode, stdout_sha256=digest(raw),
                          stderr_sha256=digest(error), meta_sha256=digest(meta) if meta.exists() else None)
assert outputs['old'] == outputs['new'], 'Refusal changed'
receipt = dict(old_binary_sha256=digest(args.old), new_binary_sha256=digest(args.new),
               runner_sha256=digest(__file__), flags=flags,
               rows=[dict(source=str(args.source), source_sha256=digest(args.source),
                          same_refusal=outputs['old']['returncode'] > 0,
                          same_frontend_outcome=True, byte_identical=True, renaming={}, outputs=outputs)],
               scope='Identical frontend outcome on an input adjudicated invalid; some invalidity is checked later by classify. Never counts as a solved ontology.')
(args.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
