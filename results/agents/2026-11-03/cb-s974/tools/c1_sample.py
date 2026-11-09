"""Pick the C1 regression-pool sample: 300 of the 1,708 admitted inputs of
.work/v152-correctness-1920/full-candidate-inputs-ws.json, uniformly at
random with seed 974, excluding the 16 held-out inputs (measured
separately). Prints one `ontology<TAB>path` line per input, sorted."""
import json, random
R = '/mnt/data2/workspaces/leechuck/software/kobayashi-marust/.work/v152-correctness-1920/'
rows = json.load(open(R + 'full-candidate-inputs-ws.json'))['inputs']
held = {f'ore_ont_{n}' for n in '4903 11647 4796 3917 11378 12191 9151 9577 6132 9899 16315 10838 3087 7557 12128 10926'.split()}
ok = [r for r in rows if r['input_admission'] == 'checks_passed' and r['ontology'] not in held]
for r in sorted(random.Random(974).sample(ok, 300), key=lambda r: r['ontology']):
    print(r['ontology'] + '\t' + r['path'])
