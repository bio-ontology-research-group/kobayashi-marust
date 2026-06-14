#!/usr/bin/env python3
"""Emit the hypertableau TInput JSON for an ontology, reusing the exact
front-end + cb_to_ht conversion that route.py uses. Lets us cache a hard
ontology's TInput once and then iterate on the `tableau_cli` binary (heuristic
tuning, absorption, pseudo-model caching) without re-parsing.

Usage:  python3 tab_emit.py ontology.ofn > tin.json
"""
import json
import sys

import cb_to_ht
import frontend


def main():
    if len(sys.argv) != 2:
        print("usage: tab_emit.py ontology.ofn", file=sys.stderr)
        sys.exit(2)
    ofn = sys.argv[1]
    clauses = frontend.ofn_to_clauses(ofn)
    rbox = frontend.ofn_rbox(ofn)
    tin = cb_to_ht.convert(clauses, rbox)
    # report fragment status on stderr (does not pollute the JSON on stdout)
    print("concepts=%d roles=%d clauses=%d fenced=%d dropped=%d inverse=%s nominals=%d"
          % (len(tin["concepts"]), len(tin["roles"]), len(tin["clauses"]),
             len(tin["fenced"]), len(tin["dropped"]), tin["inverse"],
             len(tin["nominals"])), file=sys.stderr)
    json.dump(tin, sys.stdout)


if __name__ == "__main__":
    main()
