#!/usr/bin/env python3
"""Freeze profile/size-selected input panel without inspecting KM performance."""
import csv
import math
from pathlib import Path

root = Path(__file__).resolve().parents[2]
profiles = root / 'paper/benchmark/generated/profiles'
candidates = []
for p in profiles.glob('*.tsv'):
    records = [line.split('\t') for line in p.read_text().splitlines()]
    m = {r[1]:r[2] for r in records if r[0]=='M'}
    flags = {r[1]:r[2]=='true' for r in records if r[0]=='P'}
    if flags.get('OWL2DL') and m.get('data_properties')=='0' and int(m.get('logical_axioms',0)) >= 200:
        candidates.append(dict(id=p.stem, profile='EL' if flags.get('OWL2EL') else 'DL',
            logical_axioms=int(m['logical_axioms']), classes=m['classes'],
            sha256=m['source_sha256'], path=m['source']))
selected = []
for profile in ('EL','DL'):
    for target in (1000,10000,100000):
        row = min((r for r in candidates if r['profile']==profile),
                  key=lambda r:(abs(math.log(r['logical_axioms']/target)),r['id']))
        selected.append(dict(target_axioms=target,**row))
with (Path(__file__).parent/'incremental-panel.tsv').open('w') as f:
    w = csv.DictWriter(f,fieldnames=list(selected[0]),delimiter='\t')
    w.writeheader();w.writerows(selected)
