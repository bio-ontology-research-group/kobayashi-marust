import json
from pathlib import Path
from justification_corrections import validate
c=json.loads(Path('justification-comparison-stream-v4-config.json').read_text())
originals={s['label']:s for s in c['sources']+c['km_final_sources']}
def source(s):return dict(spec=s,manifest=json.loads((Path(s['manifest_root'])/'driver-manifest.json').read_text()))
rows=[]
for s in c['common_corrections']:
 issues=validate(source(originals[s['replaces']]),source(s));rows.append(dict(label=s['label'],issues=issues))
Path('binding-validation.json').write_text(json.dumps(rows,indent=2)+'\n')
assert all(not r['issues'] for r in rows),rows
print('ALL FOUR CORRECTION BINDINGS PASS')
