#!/usr/bin/env python3
"""Delta-debug an OFN ontology against Konclude's expressivity summary.

ORE functional-syntax inputs contain one top-level axiom per line.  Prefixes,
the ontology wrapper, and declarations are held fixed; ddmin removes groups of
the remaining axioms while preserving an exact official expressivity code.
The output is a small, executable witness for otherwise opaque preprocessing
effects in ``COntologyInspector``.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile


def split_input(path):
    fixed_before = []
    declarations = []
    candidates = []
    fixed_after = []
    in_ontology = False
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            stripped = line.strip()
            if not in_ontology:
                fixed_before.append(line)
                if stripped.startswith("Ontology("):
                    in_ontology = True
                continue
            if stripped == ")":
                fixed_after.append(line)
                in_ontology = False
            elif stripped.startswith("Declaration("):
                declarations.append(line)
            elif stripped:
                candidates.append(line)
            else:
                fixed_before.append(line)
    if not fixed_after:
        raise RuntimeError("could not find the closing Ontology parenthesis")
    return fixed_before, declarations, candidates, fixed_after


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--ontology", required=True)
    parser.add_argument("--binary", required=True)
    parser.add_argument("--probe", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument(
        "--pin-pattern",
        help="regular expression for axioms that ddmin must retain",
    )
    parser.add_argument("--timeout", type=float, default=30.0)
    args = parser.parse_args()

    before, declarations, candidates, after = split_input(args.ontology)
    scratch = os.environ.get("SLURM_TMPDIR") or tempfile.gettempdir()
    trial_path = os.path.join(scratch, "expressivity-ddmin.ofn")
    cache = {}
    calls = [0]
    pin_re = re.compile(args.pin_pattern) if args.pin_pattern else None
    pinned = {
        index for index, axiom in enumerate(candidates) if pin_re and pin_re.search(axiom)
    }

    def selected_indices(removable):
        return sorted(pinned.union(removable))

    def render(removable, path):
        indices = selected_indices(removable)
        with open(path, "w", encoding="utf-8") as handle:
            handle.writelines(before)
            handle.writelines(declarations)
            handle.writelines(candidates[index] for index in indices)
            handle.writelines(after)

    def expression(removable):
        key = tuple(removable)
        if key in cache:
            return cache[key]
        render(removable, trial_path)
        command = [
            sys.executable,
            args.probe,
            "--binary",
            args.binary,
            "--ontology",
            trial_path,
            "--timeout",
            str(args.timeout),
        ]
        completed = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            encoding="utf-8",
            timeout=args.timeout + 10,
        )
        calls[0] += 1
        try:
            record = json.loads(completed.stdout)
            result = record.get("expressivity") if record.get("status") == "ok" else None
        except (ValueError, TypeError):
            result = None
        cache[key] = result
        print(
            "probe=%d axioms=%d expression=%s"
            % (calls[0], len(selected_indices(removable)), result),
            flush=True,
        )
        return result

    current = [index for index in range(len(candidates)) if index not in pinned]
    initial = expression(current)
    if initial != args.target:
        raise RuntimeError("initial expression %r != target %r" % (initial, args.target))

    granularity = 2
    while len(current) >= 2:
        chunk_size = (len(current) + granularity - 1) // granularity
        reduced = False
        for start in range(0, len(current), chunk_size):
            complement = current[:start] + current[start + chunk_size :]
            if not complement:
                continue
            if expression(complement) == args.target:
                current = complement
                granularity = max(2, granularity - 1)
                reduced = True
                break
        if not reduced:
            if granularity >= len(current):
                break
            granularity = min(len(current), granularity * 2)

    render(current, args.output)
    selected = selected_indices(current)
    print(
        json.dumps(
            {
                "input_candidates": len(candidates),
                "pinned_candidates": len(pinned),
                "remaining_candidates": len(selected),
                "probes": calls[0],
                "target": args.target,
                "output": os.path.abspath(args.output),
                "remaining_axioms": [candidates[index].strip() for index in selected],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
