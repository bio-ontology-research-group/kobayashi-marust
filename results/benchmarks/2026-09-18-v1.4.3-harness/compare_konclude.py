#!/usr/bin/env python3
"""Compare recovered KM answers with Konclude using the pinned harness normalizer.

This comparison deliberately requires no special-class groups. If either
normalizer detects one, report needs_review rather than silently excluding it.
"""
import argparse
import gzip
import importlib.util
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('panel', type=Path)
parser.add_argument('references', type=Path)
parser.add_argument('--normalizer', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
spec = importlib.util.spec_from_file_location('harness_normalizer', args.normalizer)
normalizer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(normalizer)
results = []
for directory in sorted(args.references.iterdir()):
    if not directory.is_dir():
        continue
    candidates = list(args.panel.glob('*/output/' + directory.name + '.json*'))
    if len(candidates) != 1:
        continue
    candidate = candidates[0]
    cases = [json.loads(line) for line in
             (candidate.parent.parent / 'results.jsonl').read_text().splitlines()]
    if not any(r.get('ont') == directory.name and r.get('outcome') == 'ok' for r in cases):
        continue
    result = dict(ontology=directory.name, reference=str(directory), status='unverified')
    receipt = directory / 'exit-code'
    taxonomy = directory / 'taxonomy.owl'
    if not taxonomy.exists():
        taxonomy = directory / 'taxonomy.owl.gz'
    if receipt.exists() and receipt.read_text().strip() == '0' and taxonomy.exists():
        km = json.loads(gzip.decompress(candidate.read_bytes()) if candidate.suffix == '.gz' else candidate.read_bytes())
        reference = normalizer.parse_owx(str(taxonomy))
        expected = reference.closure()
        observed = set(map(tuple, km['subsumptions']))
        result.update(missing=sorted(expected-observed), extra=sorted(observed-expected),
                      relations=len(expected), unsat=sorted(reference.unsat),
                      thing_equiv=sorted(reference.thing_equiv))
        result['status'] = 'agree' if (km['consistent'] and not km['unsatisfiable']
            and not reference.unsat and not reference.thing_equiv and expected == observed) else 'needs_review'
    results.append(result)
args.output.write_text(json.dumps(results, indent=2) + '\n')
