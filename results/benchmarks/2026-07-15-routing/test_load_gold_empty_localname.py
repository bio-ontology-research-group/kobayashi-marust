#!/usr/bin/env python3
"""Regression: gold signature parsing must preserve empty local-name pairs.

Runs without pytest: `python3 test_load_gold_empty_localname.py` prints OK and
exits 0, or raises AssertionError.

The guarded bug: a class whose IRI ends in `#` or `/` (e.g. ore_ont_11745's
`<http://purl.org/obo/owl/UniProtKB#>`) has an *empty* local name, so its
subsumption row in a canonical `.sig.gz` is written by `ore_runone.py` as
`\tRIGHT` (a leading tab, empty left field). The matrix runners' `load_gold`
used `line.strip()` (which deletes the leading tab) followed by whitespace
`line.split()` (which drops empty fields), so that one pair vanished from the
parsed gold while every reasoner's own canonicalized output still contained it.
The result was a phantom `extra=1` and a false `unsound` verdict for EVERY
reasoner (KM, Konclude, ELK, HermiT) on any ontology with such a class. The fix
parses the tab-delimited rows faithfully, matching `ore_aggregate.load_sig`.
"""
import gzip
import os
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, "../../../oracle/ore")))

import bench_one  # noqa: E402
import bench_one_matrix_frozen  # noqa: E402

# A canonical local-name signature exactly as ore_runone.py writes it:
#   line 0        consistency flag
#   subs rows     "left\tright", sorted; an empty local name yields "\tright"
#   "#UNSAT"      marker
#   unsat rows    one local name per line
GOLD_BLOB = (
    "1\n"
    "\tPRO_000003147\n"          # empty left local name (IRI ends in `#`)
    "A1A4S6\tPRO_000002211\n"    # ordinary pair
    "GO_0000902\tThing\n"        # ->Thing, must be filtered out
    "GO_0000904\tGO_0000904\n"   # reflexive, must be filtered out
    "#UNSAT\n"
    "GO_0008046\n"
)

EXPECT_PAIRS = {("", "PRO_000003147"), ("A1A4S6", "PRO_000002211")}
EXPECT_UNSAT = {"GO_0008046"}


def write_gold(tmpdir):
    path = os.path.join(tmpdir, "konclude__ore_ont_probe.owl.sig.gz")
    with gzip.open(path, "wb") as gz:
        gz.write(GOLD_BLOB.encode("utf-8"))
    return path


def check(loader, name, path):
    consistent, pairs, unsat = loader(path)
    assert consistent is True, f"{name}: consistency flag lost"
    assert ("", "PRO_000003147") in pairs, (
        f"{name}: empty-local-name pair dropped -> phantom extra=1. got {sorted(pairs)}"
    )
    assert pairs == EXPECT_PAIRS, f"{name}: pairs {sorted(pairs)} != {sorted(EXPECT_PAIRS)}"
    assert unsat == EXPECT_UNSAT, f"{name}: unsat {sorted(unsat)} != {sorted(EXPECT_UNSAT)}"


def main():
    with tempfile.TemporaryDirectory() as tmpdir:
        path = write_gold(tmpdir)
        check(bench_one_matrix_frozen.load_gold, "bench_one_matrix_frozen", path)
        check(bench_one.load_gold, "bench_one", path)
    print("OK")


if __name__ == "__main__":
    main()
