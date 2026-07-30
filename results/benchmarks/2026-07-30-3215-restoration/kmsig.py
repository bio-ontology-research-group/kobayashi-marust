#!/usr/bin/env python3
"""Compare a `km classify` JSON output against a Konclude gold `.sig[.gz]`.

The KM side goes through the repository canonicaliser (`ore_canon.py`, the same
one the ORE harness uses): SCC condensation for equivalences, full transitive
closure, owl:Thing / owl:Nothing and unsatisfiable-class pairs dropped. The gold
`.sig` file is already in that canonical form, so it is read directly.

Usage: kmsig.py <km-classify.json> <konclude__ore_ont_N.owl.sig.gz>
"""
import gzip
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import ore_canon  # noqa: E402


def read_gold(path):
    op = gzip.open if str(path).endswith(".gz") else open
    with op(path, "rt") as fh:
        lines = fh.read().split("\n")
    consistent = lines[0].strip() == "1"
    subs = set()
    unsat = set()
    in_unsat = False
    for ln in lines[1:]:
        if not ln:
            continue
        if ln == "#UNSAT":
            in_unsat = True
            continue
        if in_unsat:
            unsat.add(ln.strip())
        else:
            a, _, b = ln.partition("\t")
            subs.add((a, b))
    return consistent, subs, unsat


def main():
    km_path, gold_path = sys.argv[1], sys.argv[2]
    kc, ks, ku, capped = ore_canon.canonicalize(
        pathlib.Path(km_path).read_text(), "json"
    )
    gc, gs, gu = read_gold(gold_path)
    missing = gs - ks
    extra = ks - gs
    print(f"km pairs   : {len(ks)}")
    print(f"gold pairs : {len(gs)}")
    print(f"missing    : {len(missing)}")
    print(f"extra      : {len(extra)}")
    print(f"km unsat   : {len(ku)}  gold unsat: {len(gu)}")
    print(f"unsat missing: {len(gu - ku)}  unsat extra: {len(ku - gu)}")
    print(f"consistent : km={kc} gold={gc}  closure_capped={capped}")
    ok = not missing and not extra and ku == gu and kc == gc and not capped
    print("EXACT_MATCH" if ok else "MISMATCH")
    for p in sorted(missing)[:5]:
        print("  missing:", p)
    for p in sorted(extra)[:5]:
        print("  extra  :", p)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
