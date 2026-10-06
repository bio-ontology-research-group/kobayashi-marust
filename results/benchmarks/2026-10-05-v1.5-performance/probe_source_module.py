"""Diagnostic source locality-module size; never authorizes production projection."""
import argparse
from collections import defaultdict, deque
import hashlib
import json
from pathlib import Path


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def analyze(old, new, focus, *, include_axioms=False):
    queries = sorted(focus)
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
    active = []
    for key, axiom in after.items():
        for body, _ in axiom_rules(axiom):
            bits = full
            for premise in body:
                bits &= values.get(premise, 0)
            if bits:
                active.append(key)
                break
    result = dict(queries=len(queries), source_axioms=len(after), module_axioms=len(active),
                  selected_axiom_key_sha256=hashlib.sha256(canonical(sorted(active)).encode()).hexdigest())
    if include_axioms:
        result["selected_axioms"] = [after[key] for key in sorted(active)]
    return result

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--focus', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source = json.loads(args.source.read_text())
    focus = json.loads(args.focus.read_text())['affected_names']
    assert set(focus) <= {source['concepts'][q] for q in source['queries']}
    result = analyze(source, source, focus)
    result.update(diagnostic_only=True, source_sha256=hashlib.sha256(args.source.read_bytes()).hexdigest(),
                  focus_sha256=hashlib.sha256(args.focus.read_bytes()).hexdigest(),
                  scope='Module-size estimate only. Exact source rendering, full RBox preservation, projection certification and fresh-answer comparisons remain required.')
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
