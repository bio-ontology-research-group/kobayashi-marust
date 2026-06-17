#!/usr/bin/env python3
"""Train a decision tree that routes an ontology to the cheapest KM engine/config.

Inputs:
  --features features.jsonl   # from ont_features.py  ({"ont":..., <structural feats>})
  --results  results.jsonl    # from the bigsweep     ({"runner","ont","status","wall_s","peak_mb","match"})

Label per ontology = the *cheapest KM arm that matches gold* (min wall_s, tie-break
peak_mb), among --targets; "none" if no target arm solves it. The tree keys only on
structural features (no ontology identity), so the learned router is a general rule.

Reports honest out-of-fold routing coverage (does the predicted arm actually pass?)
versus the single-best-arm baseline and the oracle (union) ceiling, prints the tree
and feature importances, and code-generates a dependency-free `route(feat)->arm`
into route_rules.py for wiring into owl_classify.py.

    python3 route_tree.py --features features.jsonl --results results.jsonl \
        [--targets km-prod-emelim,km-prod,km-absorb,km-base,km-ht-emelim] \
        [--max-depth 6] [--min-leaf 3] [--emit route_rules.py]

Needs scikit-learn + numpy (pip install --user scikit-learn).
"""
import json, argparse, os, sys
from collections import defaultdict, Counter

DEFAULT_TARGETS = ["km-prod-emelim", "km-prod", "km-absorb", "km-base", "km-ht-emelim"]
DROP_KEYS = {"ont", "status", "err"}


def load_jsonl(path):
    rows = []
    for ln in open(path):
        ln = ln.strip()
        if ln:
            try: rows.append(json.loads(ln))
            except Exception: pass
    return rows


def build_dataset(feat_rows, res_rows, targets):
    feats = {r["ont"]: r for r in feat_rows if r.get("status") == "ok"}
    # per-ont, per-runner: (matched, wall, mem)
    perf = defaultdict(dict)
    for r in res_rows:
        perf[r["ont"]][r["runner"]] = (bool(r.get("match")),
                                       r.get("wall_s") if r.get("wall_s") is not None else 1e9,
                                       r.get("peak_mb") if r.get("peak_mb") is not None else 1e9)

    feat_keys = sorted({k for fr in feats.values() for k in fr if k not in DROP_KEYS})
    X, y, onts = [], [], []
    arm_solves = Counter(); n_oracle = 0
    for ont, fr in feats.items():
        pf = perf.get(ont, {})
        passing = [(a, pf[a][1], pf[a][2]) for a in targets if a in pf and pf[a][0]]
        for a in targets:
            if a in pf and pf[a][0]:
                arm_solves[a] += 1
        if passing:
            n_oracle += 1
            best = min(passing, key=lambda t: (t[1], t[2]))[0]
        else:
            best = "none"
        X.append([fr.get(k, 0) for k in feat_keys])
        y.append(best); onts.append(ont)
    return feat_keys, X, y, onts, perf, arm_solves, n_oracle


def realized_pass(pred, ont, perf, targets):
    """Did the routed arm actually match gold? 'none' counts as a non-solve."""
    if pred == "none":
        return False
    pf = perf.get(ont, {})
    return pred in pf and pf[pred][0]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--features", required=True)
    ap.add_argument("--results", required=True)
    ap.add_argument("--targets", default=",".join(DEFAULT_TARGETS))
    ap.add_argument("--max-depth", type=int, default=6)
    ap.add_argument("--min-leaf", type=int, default=3)
    ap.add_argument("--folds", type=int, default=5)
    ap.add_argument("--emit", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "route_rules.py"))
    args = ap.parse_args()

    try:
        import numpy as np
        from sklearn.tree import DecisionTreeClassifier, export_text
        from sklearn.model_selection import StratifiedKFold
    except Exception as e:
        sys.exit("need scikit-learn + numpy: pip install --user scikit-learn  (%s)" % e)

    targets = [t for t in args.targets.split(",") if t]
    feat_rows = load_jsonl(args.features)
    res_rows = load_jsonl(args.results)
    feat_keys, X, y, onts, perf, arm_solves, n_oracle = build_dataset(feat_rows, res_rows, targets)
    if not X:
        sys.exit("no joined rows — check that features.jsonl and results.jsonl ont keys align")
    X = np.array(X, dtype=float); y = np.array(y)
    N = len(y)

    print("=== dataset ===")
    print("ontologies with features+results:", N)
    print("feature columns (%d):" % len(feat_keys), feat_keys)
    print("label distribution:", dict(Counter(y)))
    print("per-arm solves (any-order):", dict(arm_solves))
    best_arm = max(targets, key=lambda a: arm_solves[a])
    print("single-best-arm baseline: %s solves %d/%d (%.1f%%)" %
          (best_arm, arm_solves[best_arm], N, 100 * arm_solves[best_arm] / N))
    print("oracle (any target solves): %d/%d (%.1f%%)" % (n_oracle, N, 100 * n_oracle / N))

    # honest out-of-fold routing coverage
    classes = sorted(set(y))
    can_cv = len(classes) > 1 and all(list(y).count(c) >= args.folds for c in classes)
    if can_cv:
        skf = StratifiedKFold(n_splits=args.folds, shuffle=True, random_state=0)
        oof_solved = 0; oof_acc = 0
        for tr, te in skf.split(X, y):
            clf = DecisionTreeClassifier(max_depth=args.max_depth, min_samples_leaf=args.min_leaf,
                                         class_weight="balanced", random_state=0)
            clf.fit(X[tr], y[tr])
            pred = clf.predict(X[te])
            for i, idx in enumerate(te):
                if pred[i] == y[idx]: oof_acc += 1
                if realized_pass(pred[i], onts[idx], perf, targets): oof_solved += 1
        print("\n=== %d-fold out-of-fold ===" % args.folds)
        print("label accuracy:        %.1f%%" % (100 * oof_acc / N))
        print("ROUTED coverage (predicted arm really passes): %d/%d (%.1f%%)" %
              (oof_solved, N, 100 * oof_solved / N))
        print("  vs single-best-arm %.1f%%   vs oracle %.1f%%" %
              (100 * arm_solves[best_arm] / N, 100 * n_oracle / N))
    else:
        print("\n(skipping CV: a class has < folds members)")

    # final tree on all data
    clf = DecisionTreeClassifier(max_depth=args.max_depth, min_samples_leaf=args.min_leaf,
                                 class_weight="balanced", random_state=0)
    clf.fit(X, y)
    print("\n=== feature importances ===")
    for k, imp in sorted(zip(feat_keys, clf.feature_importances_), key=lambda t: -t[1]):
        if imp > 0:
            print("  %-18s %.3f" % (k, imp))
    print("\n=== decision tree ===")
    print(export_text(clf, feature_names=feat_keys, max_depth=args.max_depth))

    if args.emit:
        emit_router(clf, feat_keys, args.emit)
        print("wrote dependency-free router -> %s" % args.emit)


def emit_router(clf, feat_keys, path):
    """Code-generate a pure-Python route(feat: dict) -> arm from the fitted tree."""
    t = clf.tree_
    classes = list(clf.classes_)
    lines = ["# AUTO-GENERATED by route_tree.py — do not edit by hand.",
             "# route(feat) -> KM arm name; feat is the ont_features.py dict.",
             "", "def route(feat):"]

    def rec(node, depth):
        ind = "    " * (depth + 1)
        if t.feature[node] != -2:  # internal
            fname = feat_keys[t.feature[node]]
            thr = t.threshold[node]
            lines.append("%sif feat.get(%r, 0) <= %.6g:" % (ind, fname, thr))
            rec(t.children_left[node], depth + 1)
            lines.append("%selse:" % ind)
            rec(t.children_right[node], depth + 1)
        else:
            cls = classes[int(t.value[node][0].argmax())]
            lines.append("%sreturn %r" % (ind, cls))

    rec(0, 0)
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
