"""Reconstruct 4669's extra entailments from references and checked source subsets.
Run with the path to paper/benchmark/runners/full_iri_fingerprint.py.
The three source-subset proof receipts must already have passed CheckSubclass.
"""
import gzip
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
role = 'http://purl.obolibrary.org/obo/BFO_0000051'
with gzip.open(root / 'source.owl.gz', 'rt') as f:
    source = f.read()
with gzip.open(root / 'elk.normalized.json.gz', 'rt') as f:
    baseline = json.load(f)
definitions = {
    filler: name for name, r, filler in re.findall(
        r'EquivalentClasses\(<([^>]+)> ObjectComplementOf\(ObjectSomeValuesFrom\(<([^>]+)> <([^>]+)>\)\)\)', source
    ) if r == role
}
positive = {tuple(e) for e in baseline['subsumptions']}
existentials = {
    (a, b) for a, r, b in re.findall(
        r'SubClassOf\(<([^>]+)> ObjectSomeValuesFrom\(<([^>]+)> <([^>]+)>\)\)', source
    ) if r == role
}
assert f'TransitiveObjectProperty(<{role}>)' in source
negative = {
    (definitions[b], definitions[a]) for a, b in positive | existentials
    if a in definitions and b in definitions
}
top = 'http://phenoscape.org/not_has_part/http://www.w3.org/2002/07/owl#Thing'
assert f'EquivalentClasses(<{top}> ObjectComplementOf(ObjectSomeValuesFrom(<{role}> owl:Thing)))' in source
negative.update((top, n) for n in definitions.values() if n != top)
for folder in ['hermit-probe', 'hermit-GO_0043630', 'hermit-GO_0048610']:
    proof = json.loads((root / folder / 'verification.json').read_text())
    assert proof['exit_code'] == 0
    assert proof['stdout'].strip() == 'source_subset=true consistent=true entailed=true'
    negative.add(tuple(proof['command'][-2:]))
baseline['subsumptions'] = sorted(positive | negative)
with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    (tmp / 'source.owl').write_text(source)
    (tmp / 'input.json').write_text(json.dumps(baseline))
    subprocess.run([sys.executable, sys.argv[1], '--input', str(tmp / 'input.json'),
                    '--format', 'json', '--source-ontology', str(tmp / 'source.owl'),
                    '--output-prefix', str(tmp / 'expected')], check=True)
    with gzip.open(tmp / 'expected.nodes.tsv.gz', 'rb') as f:
        expected = f.read()
    with gzip.open(root / 'km.nodes.tsv.gz', 'rb') as f:
        assert expected == f.read()
print('All 48158 KM taxonomy rows match the reconstructed entailments.')
