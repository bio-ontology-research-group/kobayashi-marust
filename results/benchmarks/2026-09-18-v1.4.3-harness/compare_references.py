#!/usr/bin/env python3
"""Compare KM JSON with completed FullIriClassifier reference receipts.

Incomplete or failed reference runs are retained as unverified. Inconsistent
verdicts are compared before taxonomy, whose representation differs by tool.
"""
import argparse
import gzip
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('panel', type=Path)
parser.add_argument('references', nargs='+', type=Path)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
results = []
for candidate in sorted(args.panel.glob('*/output/*.json*')):
    ontology = candidate.name.removesuffix('.gz').removesuffix('.json')
    cases = candidate.parent.parent / 'results.jsonl'
    if cases.exists():
        completed = []
        for line in cases.read_text().splitlines():
            try:
                row = json.loads(line)
            except json.JSONDecodeError:
                continue  # A partial tail is not a completed observation.
            if row.get('kind') == 'case' and row.get('ont') == ontology:
                completed.append(row)
        if not completed or completed[-1]['outcome'] != 'ok':
            continue
    km = json.loads(gzip.decompress(candidate.read_bytes()) if candidate.suffix == '.gz' else candidate.read_bytes())
    if not isinstance(km.get('consistent'), bool):
        continue
    for root in args.references:
        for receipt in sorted((root / ontology).glob('*/receipt.json')):
            meta = json.loads(receipt.read_text())
            result = dict(ontology=ontology, reference=str(receipt.parent),
                          candidate=str(candidate), reference_rc=meta['rc'])
            taxonomy = receipt.parent / 'taxonomy.tsv'
            rows = [line.replace('\\t', '\t').split('\t')
                    for line in taxonomy.read_text().splitlines()] if taxonomy.exists() else []
            verdicts = [r[1] for r in rows if r[0] == 'C' and len(r) == 2]
            if meta['rc'] != 0 or ['Z', 'complete'] not in rows or len(verdicts) != 1:
                result['status'] = 'unverified'
            elif (verdicts[0] == 'true') != km['consistent']:
                result['status'] = 'consistency_disagreement'
            elif not km['consistent']:
                result['status'] = 'agree_inconsistent'
            else:
                expected = {tuple(r[1:]) for r in rows if r[0] == 'S'}
                observed = set(map(tuple, km['subsumptions']))
                expected_unsat = {r[1] for r in rows if r[0] == 'U'}
                observed_unsat = set(km['unsatisfiable'])
                result.update(missing=sorted(expected - observed),
                              extra=sorted(observed - expected),
                              missing_unsat=sorted(expected_unsat - observed_unsat),
                              extra_unsat=sorted(observed_unsat - expected_unsat))
                result['status'] = 'agree' if not any(result[k] for k in
                    ('missing', 'extra', 'missing_unsat', 'extra_unsat')) else 'taxonomy_disagreement'
            results.append(result)
args.output.write_text(json.dumps(results, indent=2) + '\n')
