#!/usr/bin/env python3
"""Check the public batch and incremental APIs on independent ABox controls."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

P = 'http://example.org/'
def ontology(body):
    return 'Ontology(\n' + body.replace(':A', f'<{P}A>').replace(':B', f'<{P}B>').replace(':C', f'<{P}C>').replace(':D', f'<{P}D>').replace(':a', f'<{P}a>').replace(':b', f'<{P}b>') + '\n)\n'

cases = {
    'joint_disjoint': (False, ontology('DisjointClasses(:A :B)\nClassAssertion(:A :a)\nClassAssertion(:B :a)')),
    'separate_individuals': (True, ontology('DisjointClasses(:A :B)\nClassAssertion(:A :a)\nClassAssertion(:B :b)')),
    'duplicate_assertion': (True, ontology('DisjointClasses(:A :B)\nClassAssertion(:A :a)\nClassAssertion(:A :a)')),
    'compatible_joint': (True, ontology('SubClassOf(:A :C)\nSubClassOf(:B :C)\nClassAssertion(:A :a)\nClassAssertion(:B :a)')),
    'inherited_clash': (False, ontology('SubClassOf(:A :C)\nSubClassOf(:B :D)\nDisjointClasses(:C :D)\nClassAssertion(:A :a)\nClassAssertion(:B :a)')),
    'asserted_bottom': (False, ontology('SubClassOf(:A owl:Nothing)\nClassAssertion(:A :a)')),
}

def main():
    p = argparse.ArgumentParser()
    p.add_argument('binary', type=Path)
    p.add_argument('output', type=Path)
    a = p.parse_args()
    binary = a.binary.resolve()
    a.output.mkdir(parents=True, exist_ok=False)
    env = {k: v for k, v in os.environ.items() if not k.startswith('KM_')}
    env['KM_THREADS'] = '1'
    rows = []
    def run(name, command, expected, request=None):
        process = subprocess.run(command, input=request, text=True, capture_output=True,
                                 env=env, timeout=60)
        (a.output / (name + '.stdout')).write_text(process.stdout)
        (a.output / (name + '.stderr')).write_text(process.stderr)
        answers = [json.loads(line) for line in process.stdout.splitlines() if line]
        results = [v.get('result', v) for v in answers]
        correct = process.returncode == 0 and len(results) == len(expected)
        correct = correct and all(v.get('consistent') is want for v, want in zip(results, expected))
        # Global inconsistency suppresses any stale finite taxonomy publication.
        correct = correct and all(want or (not v.get('subsumptions') and not v.get('unsatisfiable'))
                                  for v, want in zip(results, expected))
        rows.append({'case': name, 'returncode': process.returncode, 'correct': correct,
                     'expected_consistency': expected, 'actual': results})
    for name, (expected, source) in cases.items():
        source_file = a.output / (name + '.ofn')
        source_file.write_text(source)
        for route in ['auto', 'manual']:
            run(name + '-' + route, [str(binary), 'classify', '--route', route, str(source_file.resolve())], [expected])
        run(name + '-incremental-init', [str(binary), 'incremental-source'], [expected],
            json.dumps({'op': 'init', 'functional_syntax': source}) + '\n')
    sequence = ['separate_individuals', 'joint_disjoint', 'separate_individuals',
                'inherited_clash', 'compatible_joint']
    request = ''.join(json.dumps({'op': 'init' if i == 0 else 'replace',
                                 'functional_syntax': cases[name][1]}) + '\n'
                      for i, name in enumerate(sequence))
    run('alternating-revisions', [str(binary), 'incremental-source'],
        [cases[name][0] for name in sequence], request)
    receipt = {'binary_sha256': hashlib.sha256(binary.read_bytes()).hexdigest(),
               'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'passed': sum(row['correct'] for row in rows), 'total': len(rows), 'rows': rows}
    (a.output / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'rows'}))
    return 0 if all(row['correct'] for row in rows) else 1

if __name__ == '__main__':
    raise SystemExit(main())
