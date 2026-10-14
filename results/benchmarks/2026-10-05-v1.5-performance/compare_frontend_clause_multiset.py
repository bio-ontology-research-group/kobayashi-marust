"""Audit retained frontend outputs allowing source-bound renaming and clause order only."""
import argparse
from collections import Counter
import json
from pathlib import Path
from check_empty_iri_frontend import compare, digest


def compare_clause_multisets(old, new, old_meta, new_meta):
    old_clauses, new_clauses = old['clauses'], new['clauses']
    # The strict checker binds entity and nominal-proxy names to source owners.
    # Every field other than the outer clause sequence keeps its strict contract.
    old_rest, new_rest = dict(old), dict(new)
    old_rest['clauses'], new_rest['clauses'] = [], []
    rename = compare(old_rest, new_rest, old_meta, new_meta)
    assert rename, 'No source renaming explains this clause-order difference'
    def renamed(value):
        if isinstance(value, str):
            return rename.get(value, value)
        if isinstance(value, list):
            return [renamed(item) for item in value]
        if isinstance(value, dict):
            return {rename.get(key, key): renamed(item) for key, item in value.items()}
        return value
    def multiset(clauses):
        return Counter(json.dumps(clause, sort_keys=True, separators=(',', ':'))
                       for clause in clauses)
    assert multiset(renamed(old_clauses)) == multiset(new_clauses), \
        'Clause multiplicity or clause contents changed'
    return rename


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--ontology', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    files = {label: args.directory / (args.ontology + '-' + label + suffix)
             for label, suffix in [('old', '.json'), ('new', '.json'),
                                    ('old-meta', '.json'), ('new-meta', '.json')]}
    files['old-meta'] = args.directory / (args.ontology + '-old.meta.json')
    files['new-meta'] = args.directory / (args.ontology + '-new.meta.json')
    old, new, old_meta, new_meta = [json.loads(files[key].read_text())
                                  for key in ['old', 'new', 'old-meta', 'new-meta']]
    rename = compare_clause_multisets(old, new, old_meta, new_meta)
    receipt = dict(ontology=args.ontology, passed=True, renaming=rename,
                   clause_count=len(old['clauses']), file_sha256={k:digest(v) for k,v in files.items()},
                   runner_sha256=digest(__file__), binding_checker_sha256=digest(Path(__file__).with_name('check_empty_iri_frontend.py')),
                   scope='Source-bound entity renaming and outer clause order only; clause multiplicities, ordered bodies/heads/terms, role chains and all other metadata preserved.')
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')


if __name__ == '__main__':
    main()
