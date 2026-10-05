"""Diagnostic source-expression activation; never authorizes production reuse."""
import argparse
from collections import defaultdict, deque
import hashlib
import json
from pathlib import Path


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def analyze(old, new):
    queries = sorted({old['concepts'][q] for q in old['queries']})
    assert queries == sorted({new['concepts'][q] for q in new['queries']})
    full = (1 << len(queries)) - 1
    values = {canonical({'Name': q}): 1 << i for i, q in enumerate(queries)}
    rules = set()
    visited = set()

    def expression(expr):
        key = canonical(expr)
        if key in visited:
            return key
        visited.add(key)
        if expr == 'Top':
            values[key] = full
        elif expr == 'Bottom':
            pass
        elif 'Name' in expr:
            pass
        elif 'And' in expr:
            children = tuple(sorted({expression(x) for x in expr['And']}))
            rules.add((children, key))
            for child in children:
                rules.add(((key,), child))
        elif 'Exists' in expr:
            _, filler = expr['Exists']
            child = expression(filler)
            # All roles and term positions are available in this abstraction.
            rules.add(((key,), child))
            rules.add(((child,), key))
        else:
            raise ValueError(('outside positive source fragment', expr))
        return key

    def axiom_rules(axiom):
        left, right = expression(axiom['left']), expression(axiom['right'])
        kind = axiom['kind']
        if kind == 'sub-class':
            return [((left,), right)]
        if kind == 'equivalent':
            return [((left,), right), ((right,), left)]
        if kind == 'disjoint':
            return [(tuple(sorted({left, right})), canonical('Bottom'))]
        raise ValueError(kind)

    prior = {canonical(a): a for a in old['source_axioms']}
    after = {canonical(a): a for a in new['source_axioms']}
    changed = []
    for key, axiom in (prior | after).items():
        lowered = axiom_rules(axiom)
        rules.update(lowered)
        if (key in prior) != (key in after):
            changed.extend(lowered)
    for snapshot in [old, new]:
        for _, concept in snapshot['role_domains'] + snapshot['role_ranges']:
            values[canonical({'Name': snapshot['concepts'][concept]})] = full
    rules = sorted(rules)
    users = defaultdict(list)
    for i, (body, _) in enumerate(rules):
        for premise in body:
            users[premise].append(i)
    queue = deque(range(len(rules)))
    queued = set(queue)
    while queue:
        i = queue.popleft()
        queued.remove(i)
        body, head = rules[i]
        bits = full
        for premise in body:
            bits &= values.get(premise, 0)
        previous = values.get(head, 0)
        following = previous | bits
        if previous != following:
            values[head] = following
            for dependent in users[head]:
                if dependent not in queued:
                    queue.append(dependent)
                    queued.add(dependent)
    affected = 0
    for body, _ in changed:
        bits = full
        for premise in body:
            bits &= values.get(premise, 0)
        affected |= bits
    names = [q for i, q in enumerate(queries) if affected >> i & 1]
    return dict(public_queries=len(queries), source_axioms_removed=len(prior.keys()-after.keys()),
                source_axioms_added=len(after.keys()-prior.keys()), abstract_rules=len(rules),
                affected_queries=len(names), potentially_reusable_queries=len(queries)-len(names),
                affected_names=names)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('old', type=Path)
    parser.add_argument('new', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    result = analyze(json.loads(args.old.read_text()), json.loads(args.new.read_text()))
    result.update(diagnostic_only=True,
                  inputs={str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in [args.old, args.new]},
                  limitations='Source abstraction only. Typed side-state equivalence, source metadata completeness, fresh-answer comparison and Lean certification are not established. No production reuse authorized.')
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'affected_names'}))
