#!/usr/bin/env python3
"""Self-check for the routing-analyzer correctness predicates.

Runs without pytest:
    python3 results/benchmarks/2026-07-15-routing/test_analyze_routing.py

Guards the regression where analyze_auto.exact / analyze_rechecks.exact counted
a `nogold` verdict as an exact/correct result. `nogold` only means
canonicalization succeeded on a no-authoritative-gold input; promoting it
inflates the reported correct count with unadjudicated ontologies and
contradicts the strict analyzer (analyze_matrix.is_correct) and the
gold-adjudication / hard-residual docs.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import analyze_auto  # noqa: E402
import analyze_rechecks  # noqa: E402

# an ontology on the module's adjudicated-inconsistent allow-list
ADJ = next(iter(analyze_auto.ADJUDICATED_INCONSISTENT))
OTHER = "ore_ont_99999.owl"


def check_exact(exact, label):
    # nogold is NOT correctness, even when the run succeeded
    assert exact(OTHER, {"status": "ok", "verdict": "nogold"}) is False, label
    assert exact(ADJ, {"status": "ok", "verdict": "nogold"}) is False, label

    # a byte-identical gold match IS correctness
    assert exact(OTHER, {"status": "ok", "verdict": "match"}) is True, label

    # a match verdict on a non-ok run is not correctness
    assert exact(OTHER, {"status": "timeout", "verdict": "match"}) in (False, None), label

    # an adjudicated-inconsistent ont proven inconsistent IS correctness
    assert exact(ADJ, {"status": "ok", "verdict": "disagree",
                       "consistent": False}) is True, label

    # a plain disagreement is not correctness
    assert exact(OTHER, {"status": "ok", "verdict": "disagree",
                         "consistent": True}) in (False, None), label

    # consistency=False alone does not rescue a non-adjudicated ont
    assert exact(OTHER, {"status": "ok", "verdict": "disagree",
                         "consistent": False}) in (False, None), label


def check():
    check_exact(analyze_auto.exact, "analyze_auto.exact")
    check_exact(analyze_rechecks.exact, "analyze_rechecks.exact")
    print("analyze_auto/analyze_rechecks exact(): OK (nogold not promoted)")


if __name__ == "__main__":
    check()
