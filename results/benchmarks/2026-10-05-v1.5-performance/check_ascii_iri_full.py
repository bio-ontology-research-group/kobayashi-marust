"""Compare exact grammar acceptance/errors on every frozen source; no solve claim."""
import json
import os
from pathlib import Path
import subprocess
from measure_classification import digest
import tree_watchdog as watchdog

root = Path(__file__).resolve().parent
manifest_path = root / 'full-candidate-inputs.json'
manifest = json.loads(manifest_path.read_text())
inventory_path = root / 'ascii-iri-artifact.json'
inventory = json.loads(inventory_path.read_text())
binary = root / inventory['binary']
assert digest(binary) == inventory['binary_sha256']
assert digest(manifest_path) == inventory['input_manifest_sha256']
assert len(manifest['inputs']) == 1920
task = int(os.environ['SLURM_ARRAY_TASK_ID'])
rows = manifest['inputs'][task * 32:(task + 1) * 32]
assert len(rows) == 32
dest = root / ('ascii-iri-full-' + os.environ['SLURM_ARRAY_JOB_ID'])
summary_path = dest / 'chunks' / (str(task) + '.json')
summary_path.parent.mkdir(parents=True, exist_ok=True)
summary = dict(status='running', diagnostic_only=True, release_approved=False,
    input_manifest_sha256=digest(manifest_path), inventory_sha256=digest(inventory_path),
    runner_sha256=digest(__file__), timeout_s_per_arm=240, memory_gib=20, cpus=1, outcomes=[])
def publish():
    temporary = summary_path.with_suffix('.part')
    temporary.write_text(json.dumps(summary, indent=2) + '\n')
    temporary.replace(summary_path)
watchdog.protect_supervisor()
publish()
for index, row in enumerate(rows):
    source = Path(row['path'])
    assert digest(source) == row['sha256']
    result = dict(ontology=row['ontology'], source_sha256=row['sha256'],
                  input_admission=row['input_admission'], arms={}, exact_agreement=False)
    output = dest / row['ontology']
    output.mkdir(parents=True, exist_ok=False)
    for arm in (['original', 'ascii'] if index % 2 == 0 else ['ascii', 'original']):
        stdout, stderr = output / (arm + '.stdout'), output / (arm + '.stderr')
        with stdout.open('wb') as out, stderr.open('wb') as err:
            proc = subprocess.Popen([str(binary), arm, str(source)], stdout=out, stderr=err,
                stdin=subprocess.DEVNULL, preexec_fn=watchdog.child_preexec)
            watched = watchdog.monitor(proc, timeout=240, memcap_bytes=20 * 1024**3)
        result['arms'][arm] = dict(status=watched.status, exit_code=proc.returncode,
            wall_s=watched.wall_s, peak_bytes=watched.peak_bytes,
            stdout_sha256=digest(stdout), stderr_sha256=digest(stderr))
    assert digest(source) == row['sha256']
    arms = result['arms']
    if all(a['status'] == 'ok' and a['exit_code'] == 0 for a in arms.values()):
        result['exact_agreement'] = (output / 'original.stdout').read_bytes() == (output / 'ascii.stdout').read_bytes()
    summary['outcomes'].append(result)
    publish()
summary['status'] = 'complete'
publish()
