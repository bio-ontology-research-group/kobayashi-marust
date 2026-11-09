"""List pool inputs where one binary has DROPPED > 0 and v1.5.3 has DROPPED 0.

usage: python3 -I compare.py HEAD.jsonl V153.jsonl [BRANCH.jsonl]
Halves: held-out = the 585 inputs of the S1 preview records
(.work/v155-preview-cert/data/heldout-rc-54897407), design = the rest.
"""
import glob, json, sys
ROOT = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust'
held = set()
for f in glob.glob(f'{ROOT}/.work/v155-preview-cert/data/heldout-rc-54897407/*.json'):
    held |= {x['ontology'] for x in json.load(open(f))['outcomes']}
load = lambda p: {r['ontology']: r for r in map(json.loads, open(p)) if True}
head = load(sys.argv[1]); v153 = load(sys.argv[2])
branch = load(sys.argv[3]) if len(sys.argv) > 3 else {}
def fmt(r):
    if r is None: return 'not run'
    if r['dropped'] is None: return f"no answer (rc {r['rc']}, {r['wall']} s)"
    return f"DROPPED {r['dropped']} ({r['wall']} s)"
rows = []
for name, r in sorted(head.items()):
    if (r['dropped'] or 0) > 0 or r['dropped'] is None:
        v = v153.get(name)
        if v is not None and v['dropped'] == 0:
            rows.append((name, 'held-out' if name in held else 'design', fmt(r), fmt(v), fmt(branch.get(name))))
print(f"head records {len(head)}, v1.5.3 records {len(v153)}, held-out {len(held)}")
print("| input | half | head 775223bf | v1.5.3 | branch |")
print("|---|---|---|---|---|")
for row in rows: print("| " + " | ".join(row) + " |")
