#!/usr/bin/env python3
"""Canonicalise one KM JSON taxonomy into the ORE ``.sig.gz`` format."""

import gzip
import hashlib
import json
import os
import sys

sys.path.insert(0, os.path.expanduser("~/bench/ore_harness"))
from ore_canon import canonicalize  # noqa: E402


def main() -> None:
    source, destination = sys.argv[1:3]
    with open(source, encoding="utf-8") as handle:
        text = handle.read()
    consistent, subsumptions, unsatisfiable, capped = canonicalize(text, "json")
    signature = "\n".join(f"{sub}\t{sup}" for sub, sup in sorted(subsumptions))
    unsat_signature = "\n".join(sorted(unsatisfiable))
    blob = (
        ("1" if consistent else "0")
        + "\n"
        + signature
        + "\n#UNSAT\n"
        + unsat_signature
    ).encode()
    with gzip.open(destination, "wb") as handle:
        handle.write(blob)
    print(
        json.dumps(
            {
                "consistent": consistent,
                "n_sub": len(subsumptions),
                "n_unsat": len(unsatisfiable),
                "capped": capped,
                "sig_sha": hashlib.sha256(blob).hexdigest(),
            }
        )
    )


if __name__ == "__main__":
    main()
