"""Compare one KM JSON taxonomy with the pinned references of its input.

usage: python3 -I compare_ref.py ONTOLOGY KM_JSON OUT_DIR

Looks up the reference directory of ONTOLOGY (e.g. ore_ont_4903) in
.work/v152-correctness-1920/full-candidate-inputs-ws.json, canonicalizes
KM_JSON against its signature.tsv with the audit's canonicalize.py, and
compares the result with every reference whose audit outcome is
`canonicalized_requires_comparison` (compare_taxonomies.compare). Prints
one JSON line per reference.
"""
import json, subprocess, sys
from pathlib import Path

ROOT = Path('/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/v152-correctness-1920')
sys.path.insert(0, str(ROOT))
from compare_taxonomies import compare  # noqa: E402

ont, km_json, out = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
out.mkdir(parents=True, exist_ok=True)
rows = json.loads((ROOT / 'full-candidate-inputs-ws.json').read_text())
rows = rows if isinstance(rows, list) else rows.get('inputs', rows)
row = next(r for r in rows if r['ontology'] == ont)
ref = Path(row['reference_directory'])
audit = json.loads((ref / 'audit.json').read_text())
prefix = out / f'{ont}.canonical'
subprocess.run([sys.executable, str(ROOT / 'canonicalize.py'), '--input', str(km_json),
                '--format', 'km-json', '--signature', str(ref / 'signature.tsv'),
                '--output-prefix', str(prefix),
                '--fingerprint-script', str(ROOT / 'full_iri_fingerprint.py')], check=True)
answer = json.loads(Path(str(prefix) + '.validated.json').read_text())
for name in ['konclude', 'hermit', 'openllet', 'jfact']:
    if audit['outcomes'].get(name, {}).get('status') != 'canonicalized_requires_comparison':
        continue
    result = compare(answer, json.loads((ref / f'{name}.validated.json').read_text()))
    print(json.dumps(dict(ontology=ont, reference=name, **{k: result.get(k) for k in ('status', 'agreement')},
                          **{k: v for k, v in result.items() if k.startswith(('missing', 'extra', 'only', 'left_count', 'right_count'))})))
