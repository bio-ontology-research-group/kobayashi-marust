"""Fixture-bounded source-module rendering experiment, never production routing.

Accept only expanded, declaration-covered, collision-free names and one axiom
per line. Preserve every non-TBox line. Check the all-axiom reconstruction
against the original fresh answer before trusting a reduced-module comparison.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from probe_source_module import analyze
import tree_watchdog as watchdog


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def render(source, axioms, expected_count):
    keep, owners, tbox_count = [], {}, 0
    allowed = {'Declaration', 'SubObjectPropertyOf', 'ObjectPropertyDomain',
               'ObjectPropertyRange', 'InverseObjectProperties', 'TransitiveObjectProperty'}
    tbox = {'SubClassOf', 'EquivalentClasses', 'DisjointClasses'}
    for line in source.splitlines():
        stripped = line.strip()
        if not stripped or stripped == ')' or stripped.startswith(('#', 'Prefix(', 'Ontology(')):
            keep.append(line)
            continue
        assert '"' not in stripped, 'fixture guard: literals/annotations not supported'
        keyword = stripped.split('(', 1)[0]
        assert keyword in allowed | tbox, ('unknown source premise', keyword)
        lexical = re.sub(r'<[^<>]*>', 'IRI', stripped)
        assert lexical.count('(') == lexical.count(')'), 'one complete axiom per line required'
        if keyword in tbox:
            tbox_count += 1
            continue
        keep.append(line)
        if keyword == 'Declaration':
            match = re.fullmatch(r'Declaration\((Class|ObjectProperty)\(<([^<>]+)>\)\)', stripped)
            assert match, stripped
            iri = match[2]
            name = iri.rsplit('#', 1)[-1] if '#' in iri else iri.rsplit('/', 1)[-1]
            assert name and not name.startswith(('Q_', '__', 'km_src_')), name
            assert owners.get(name, iri) == iri, ('IRI collision', name)
            owners[name] = iri
    assert tbox_count == expected_count, (tbox_count, expected_count)
    while keep and not keep[-1].strip():
        keep.pop()
    assert keep[-1].strip() == ')'

    def role(expr):
        if isinstance(expr, dict) and set(expr) == {'Name'}:
            return '<' + owners[expr['Name']] + '>'
        if isinstance(expr, dict) and set(expr) == {'Inv'}:
            return 'ObjectInverseOf(' + role(expr['Inv']) + ')'
        raise ValueError(('unsupported role', expr))

    def concept(expr):
        if expr == 'Top':
            return '<http://www.w3.org/2002/07/owl#Thing>'
        if expr == 'Bottom':
            return '<http://www.w3.org/2002/07/owl#Nothing>'
        if set(expr) == {'Name'}:
            return '<' + owners[expr['Name']] + '>'
        if set(expr) == {'And'}:
            return 'ObjectIntersectionOf(' + ' '.join(map(concept, expr['And'])) + ')'
        if set(expr) == {'Exists'}:
            r, c = expr['Exists']
            return 'ObjectSomeValuesFrom(' + role(r) + ' ' + concept(c) + ')'
        raise ValueError(('unsupported concept', expr))

    operators = {'sub-class': 'SubClassOf', 'equivalent': 'EquivalentClasses', 'disjoint': 'DisjointClasses'}
    additions = [operators[a['kind']] + '(' + concept(a['left']) + ' ' + concept(a['right']) + ')'
                 for a in axioms]
    return '\n'.join(keep[:-1] + additions + [')']) + '\n', owners


def selected_signature(answer, focus=None):
    assert answer['dropped'] == 0
    return (answer['consistent'], sorted(tuple(p) for p in answer['subsumptions']
                                        if focus is None or p[0] in focus),
            sorted(n for n in answer['unsatisfiable'] if focus is None or n in focus))


def main():
    parser = argparse.ArgumentParser()
    for name in ['binary', 'source', 'typed', 'focus', 'fresh', 'previous', 'output']:
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    typed = json.loads(args.typed.read_text())
    queries = json.loads(args.focus.read_text())['affected_names']
    start = time.monotonic()
    module = analyze(typed, typed, queries, include_axioms=True)
    module_text, owners = render(args.source.read_text(), module.pop('selected_axioms'), len(typed['source_axioms']))
    preparation_s = time.monotonic() - start
    control_text, _ = render(args.source.read_text(), typed['source_axioms'], len(typed['source_axioms']))
    fresh = json.loads(args.fresh.read_text())
    previous = json.loads(args.previous.read_text())
    focus = {owners[name] for name in queries}
    env = {k:v for k,v in os.environ.items() if not k.startswith('KM_')}
    env.update(KM_HT_DDB='1', KM_HT_NATIVE_FULL='1', KM_CACHE_CONFORMANCE='1',
               KM_THREADS='1', OMP_NUM_THREADS='1', RAYON_NUM_THREADS='1', KM_TIMING='1')
    cpu = min(os.sched_getaffinity(0))
    def prepare():
        watchdog.child_preexec()
        os.sched_setaffinity(0, {cpu})
    receipt = dict(diagnostic_only=True, module=module, preparation_s=preparation_s,
                   input_hashes={k:digest(getattr(args,k)) for k in ['binary','source','typed','focus','fresh','previous']},
                   records=[], cpu=cpu, timeout_s=180, memory_gib=20,
                   scope='One-source module rendering and fresh-answer comparison; not end-to-end incremental or release evidence.')
    for label, text in [('control',control_text),('module',module_text)]:
        source_path = args.output / (label+'.ofn')
        source_path.write_text(text)
        for repetition in range(2):
            output = args.output / f'{label}-{repetition}.json'
            stderr = args.output / f'{label}-{repetition}.stderr'
            with output.open('w') as out, stderr.open('w') as err:
                started = time.monotonic()
                process = subprocess.Popen([str(args.binary.resolve()), 'classify', str(source_path.resolve())],
                                           stdout=out, stderr=err, env=env, preexec_fn=prepare)
                measured = watchdog.monitor(process, timeout=180, memcap_bytes=20*1024**3)
                elapsed = time.monotonic()-started
            assert measured.status == 'ok' and process.returncode == 0, (label,measured.status)
            answer = json.loads(output.read_text())
            selected = None if label == 'control' else focus
            agreement = selected_signature(answer,selected) == selected_signature(fresh,selected)
            merged_agreement = None
            merge_s = None
            if label == 'module':
                started = time.monotonic()
                merged = dict(consistent=answer['consistent'], dropped=0,
                    subsumptions=[p for p in previous['subsumptions'] if p[0] not in focus] +
                                 [p for p in answer['subsumptions'] if p[0] in focus],
                    unsatisfiable=[n for n in previous['unsatisfiable'] if n not in focus] +
                                  [n for n in answer['unsatisfiable'] if n in focus])
                merge_s = time.monotonic()-started
                merged_agreement = selected_signature(merged) == selected_signature(fresh)
                assert merged_agreement, 'retained-row merge differs from full fresh answer'
            receipt['records'].append(dict(label=label,repetition=repetition,wall_s=elapsed,
                                           merged_full_agreement=merged_agreement,merge_s=merge_s,
                                           agreement=agreement,answer_sha256=digest(output),source_sha256=digest(source_path)))
            (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
            assert agreement, (label,'fresh-answer mismatch')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
