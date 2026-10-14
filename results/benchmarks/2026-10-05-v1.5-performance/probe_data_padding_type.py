"""Read-only feasibility probe; a witness is not a production admission certificate.

Try a single ordinary-class seed and close atomic superclass implications.
Independently check every source GCI on the resulting edgeless data-node type.
This incomplete search never changes the ontology or the reasoner's guards.
"""
import argparse
import hashlib
import json
from pathlib import Path


def evaluate(concept, positive):
    if concept == 'Top':
        return True
    if concept == 'Bottom':
        return False
    kind, value = next(iter(concept.items()))
    if kind == 'Name':
        if value.startswith('__dt__'):
            raise ValueError('Direct datatype predicate requires a value-specific interpretation')
        return value in positive
    if kind == 'Nominal':
        return False
    if kind == 'Not':
        return not evaluate(value, positive)
    if kind in ('And', 'Or'):
        values = [evaluate(item, positive) for item in value]
        return all(values) if kind == 'And' else any(values)
    if kind in ('Exists', 'Forall', 'HasSelf', 'AtLeast', 'AtMost'):
        role = value[1] if kind in ('AtLeast', 'AtMost') else value if kind == 'HasSelf' else value[0]
        if not isinstance(role, dict) or next(iter(role)) not in ('Name', 'Inverse'):
            raise ValueError('Universal or unknown role cannot use an edgeless witness')
        if kind == 'AtLeast':
            return value[0] <= 0
        if kind == 'AtMost':
            return value[0] >= 0
        return kind == 'Forall'
    raise ValueError('Unknown source constructor: ' + kind)


def holds(axiom, positive):
    left = evaluate(axiom['left'], positive)
    right = evaluate(axiom['right'], positive)
    return {'sub-class': not left or right,
            'equivalent': left == right,
            'disjoint': not (left and right)}[axiom['kind']]


def names(concept):
    if not isinstance(concept, dict):
        return set()
    kind, value = next(iter(concept.items()))
    if kind == 'Name':
        return {value} if not value.startswith('__dt__') else set()
    if kind == 'Not':
        return names(value)
    if kind in ('And', 'Or'):
        return set().union(*(names(item) for item in value))
    # Role fillers do not affect an edgeless node's truth value.
    return set()


def probe(path):
    data = json.loads(path.read_text())
    axioms = data['source_axioms']
    vocabulary = set().union(*(names(a['left']) | names(a['right']) for a in axioms))
    blank_failures = [i for i, a in enumerate(axioms) if not holds(a, set())]
    for seed in [None, *sorted(vocabulary)]:
        positive = set() if seed is None else {seed}
        while True:
            before = len(positive)
            for axiom in axioms:
                right = axiom['right']
                if (axiom['kind'] == 'sub-class' and isinstance(right, dict)
                        and 'Name' in right and evaluate(axiom['left'], positive)):
                    if right['Name'].startswith('__dt__'):
                        raise ValueError('Cannot assign a datatype predicate')
                    positive.add(right['Name'])
            if len(positive) == before:
                break
        # All axioms, including datatype-bearing axioms, must pass.
        if all(holds(axiom, positive) for axiom in axioms):
            break
    else:
        positive = None
    return dict(diagnostic_only=True, typed_input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                source_axioms_checked=len(axioms), blank_type_failures=blank_failures,
                positive_classes=sorted(positive) if positive is not None else None,
                witness_found=positive is not None, release_approved=False,
                limitations='Checks source GCIs on an edgeless padding node only. Does not prove '
                'two-sorted model transport, reverse transport, query preservation, ABox/RBox '
                'compatibility, or executable source binding. Production admission remains unchanged.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('typed_input', type=Path)
    args = parser.parse_args()
    print(json.dumps(probe(args.typed_input), indent=2))
