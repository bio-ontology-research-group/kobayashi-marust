#!/usr/bin/env python3
"""Pilot gate: complete signatures, retained/fresh and cross-reasoner agreement."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
rows = []
for case in sorted(p for p in root.iterdir() if p.is_dir()):
    gold = case / 'hermit' / 'fresh'
    reference = {p.name:p.read_bytes() for p in gold.glob('*.sig')}
    for reasoner in sorted(p for p in case.iterdir() if p.is_dir()):
        for arm in ('session','fresh'):
            path = reasoner / arm
            sigs = {p.name:p.read_bytes() for p in path.glob('*.sig')}
            complete = (path / 'COMPLETE').exists() and (path / 'exit-code').read_text().strip() == '0'
            agreement = complete and len(sigs) == 6 and sigs == reference and (gold/'COMPLETE').exists()
            own_fresh = {p.name:p.read_bytes() for p in (reasoner/'fresh').glob('*.sig')}
            rows.append(dict(case=case.name,reasoner=reasoner.name,arm=arm,
                complete=complete,states=len(sigs),agrees_with_hermit=agreement,
                agrees_with_own_fresh=complete and len(sigs)==6 and sigs==own_fresh,
                distinct_taxonomies=len(set(sigs.values())),
                signature_sha256={k:hashlib.sha256(v).hexdigest() for k,v in sigs.items()}))
print(json.dumps({'pilot_only':True,'rows':rows},indent=2))
