"""Check the fixed A < B < C pilot; not a general corpus canonicalizer."""
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'runners'))
from full_iri_fingerprint import parse_output, TOP, BOTTOM

root = Path(sys.argv[1])
expected = {('urn:v145:A', 'urn:v145:B'), ('urn:v145:A', 'urn:v145:C'), ('urn:v145:B', 'urn:v145:C')}
audits = []
for directory in sorted(p for p in root.iterdir() if p.is_dir()):
    record = json.loads((directory / 'record.json').read_text())
    assert record['status'] == 'executed_unvalidated', record
    fmt = record['output_format']
    path = directory / 'taxonomy.raw'
    if fmt in ['km-json', 'rustdl-json']:
        result = json.loads(path.read_text())
        assert result['consistent'] is True and not result.get('incomplete', False) and not result.get('dropped')
        assert not result['unsatisfiable']
        edges = result.get('subsumptions', result.get('direct_subsumptions', []))
        groups = result.get('equivalent_groups', [])
        consistent = True
    elif fmt == 'owlapi-tsv':
        lines = path.read_text().splitlines()
        assert lines[-1] == 'Z\tcomplete'
        assert not any(l.startswith('U\t') for l in lines)
        consistent = None if 'C\tunknown' in lines else 'C\ttrue' in lines
        edges = [l.split('\t')[1:] for l in lines if l.startswith('S\t')]
        groups = []
    else:
        consistent, edges, groups, unsat, declared = parse_output(path, fmt)
        assert not unsat
        assert {f'urn:v145:{c}' for c in 'ABC'} <= declared
    def iri(value):
        # This fixture declares exactly Prefix(:=<urn:v145:>).
        return 'urn:v145:' + value[1:] if value.startswith(':') else value
    pairs = {(iri(a), iri(b)) for a, b in edges}
    for group in groups:
        pairs.update((iri(a), iri(b)) for a in group for b in group if a != b)
    while True:
        added = {(a, d) for a, b in pairs for c, d in pairs if b == c and a != d}
        if added <= pairs:
            break
        pairs |= added
    pairs = {(a, b) for a, b in pairs if a not in [TOP, BOTTOM] and b not in [TOP, BOTTOM]}
    assert pairs == expected, (directory.name, pairs)
    assert consistent is True or (directory.name == 'more' and consistent is None)
    audits.append({'baseline': directory.name, 'taxonomy_matches_expected': True, 'consistent': consistent,
                   'status': 'taxonomy_only_consistency_unavailable' if consistent is None else 'passed'})
assert len(audits) == 10, 'incomplete pilot'
print(json.dumps({'scope': 'single tiny measured classification across ten baselines', 'baselines': audits}, indent=2))
