#!/usr/bin/env python3
"""Self-check for ore_aggregate.classify_vs_gold.

Runs without pytest: `python3 oracle/ore/test_ore_aggregate.py` prints OK and
exits 0, or raises AssertionError. Signatures are the (consistent, subs, unsat)
triples load_sig returns.

The regression guarded here is the pre-fix bug: when the subsumption sets were
identical but the sig_sha differed (so the fast agree-path was skipped), the old
code fell into an `else: agree` branch that ignored the unsat set and the
consistency head, silently counting genuine unsound/incomplete disagreements as
agreement.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ore_aggregate import classify_vs_gold  # noqa: E402

S = lambda *pairs: set(pairs)  # noqa: E731


def check():
    A, B, C, D = ("A", "B"), ("C", "D"), ("E", "F"), ("G", "H")

    # 1. fully identical -> agree
    g = (True, S(A, B), {"X"})
    assert classify_vs_gold(g, (True, S(A, B), {"X"})) == "agree"

    # 2. reasoner missing a gold subsumption -> incomplete
    assert classify_vs_gold(g, (True, S(A), {"X"})) == "incomplete"

    # 3. reasoner has an extra subsumption -> unsound
    assert classify_vs_gold(g, (True, S(A, B, C), {"X"})) == "unsound"

    # 4. subs identical but reasoner has an EXTRA unsat class -> unsound
    #    (THE regression: old subs-only diff returned "agree")
    assert classify_vs_gold(g, (True, S(A, B), {"X", "Y"})) == "unsound"

    # 5. subs identical but reasoner MISSES a gold unsat class -> incomplete
    #    (also mislabeled "agree" before the fix)
    assert classify_vs_gold(g, (True, S(A, B), set())) == "incomplete"

    # 6. reasoner says inconsistent, gold consistent -> both (consistency)
    assert classify_vs_gold((True, S(A, B), {"X"}), (False, set(), set())) == "both"

    # 7. gold inconsistent, reasoner consistent -> both (consistency)
    assert classify_vs_gold((False, set(), set()), (True, S(A, B), {"X"})) == "both"

    # 8. extra on one channel, missing on another -> both
    assert classify_vs_gold((True, S(A, B), {"X"}),
                            (True, S(A, C), {"X"})) == "both"

    # 9. extra unsat AND missing sub -> both
    assert classify_vs_gold((True, S(A, B), {"X"}),
                            (True, S(A), {"X", "Y"})) == "both"

    print("ore_aggregate.classify_vs_gold: OK (9 cases)")


if __name__ == "__main__":
    check()
